// 样例程序.cpp : 此文件包含 "main" 函数。程序执行将在此处开始并结束。
//

#include "pch.h"
// 随机策略
// 作者：289371298 upgraded from zhouhy
// https://www.botzone.org.cn/games/Tank2

#include "jsoncpp/json.h"
#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include<ctime>
#include <cstring>
#include <queue>
#include<stack>
#include<cstdlib>
#include<vector>
#include<algorithm>
#include<cmath>
int debugging = 0;
/*
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include <json/json.h>
#endif
*/
using std::string;using std::cin;using std::cout;using std::endl;using std::flush;using std::getline;using std::queue;

clock_t timelog[10000];
int clock_num = 0;
int viewtime;

namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

	enum GameResult
	{
		NotFinished = -2,
		Draw = -1,
		Blue = 0,
		Red = 1
	};

	enum FieldItem
	{
		None = 0,
		Brick = 1,
		Steel = 2,
		Base = 4,
		Blue0 = 8,
		Blue1 = 16,
		Red0 = 32,
		Red1 = 64,
		Water = 128
	};

	template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
	template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
	template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
	template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
	template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
	template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
	template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

	enum Action
	{
		Invalid = -2,
		Stay = -1,
		Up, Right, Down, Left,
		UpShoot, RightShoot, DownShoot, LeftShoot
	};

	// 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
	// Side（对战双方） - 0 为蓝，1 为红
	// Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
	// Turn（回合编号） - 从 1 开始

	const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

	// 基地的横坐标
	const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

	// 基地的纵坐标
	const int baseY[sideCount] = { 0, fieldHeight - 1 };

	const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
	const FieldItem tankItemTypes[sideCount][tankPerSide] = {
		{ Blue0, Blue1 },{ Red0, Red1 }
	};

	int maxTurn = 100;



#ifdef _MSC_VER
#pragma endregion

#pragma region 工具函数和类
#endif

	inline bool ActionIsMove(Action x)
	{
		return x >= Up && x <= Left;
	}

	inline bool ActionIsShoot(Action x)
	{
		return x >= UpShoot && x <= LeftShoot;
	}

	inline bool ActionDirectionIsOpposite(Action a, Action b)
	{
		return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
	}

	inline bool CoordValid(int x, int y)
	{
		return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
	}

	// 判断 item 是不是叠在一起的多个坦克
	inline bool HasMultipleTank(FieldItem item)
	{
		// 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
		// 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
		return !!(item & (item - 1));
	}

	inline int GetTankSide(FieldItem item)
	{
		return item == Blue0 || item == Blue1 ? Blue : Red;
	}

	inline int GetTankID(FieldItem item)
	{
		return item == Blue0 || item == Red0 ? 0 : 1;
	}

	// 获得动作的方向
	inline int ExtractDirectionFromAction(Action x)
	{
		if (x >= Up)
			return x % 4;
		return -1;
	}

	// 物件消失的记录，用于回退
	struct DisappearLog
	{
		FieldItem item;

		// 导致其消失的回合的编号
		int turn;

		int x, y;
		bool operator< (const DisappearLog& b) const
		{
			if (x == b.x)
			{
				if (y == b.y)
					return item < b.item;
				return y < b.y;
			}
			return x < b.x;
		}
	};

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField 主要逻辑类
#endif

	class TankField
	{
	public:
		//!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

		// 游戏场地上的物件（一个格子上可能有多个坦克）
		FieldItem gameField[fieldHeight][fieldWidth] = {};

		// 坦克是否存活
		bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

		// 基地是否存活
		bool baseAlive[sideCount] = { true, true };

		// 坦克横坐标，-1表示坦克已炸
		int tankX[sideCount][tankPerSide] = {
			{ fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
		};

		// 坦克纵坐标，-1表示坦克已炸
		int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

		// 当前回合编号
		int currentTurn = 1;

		// 我是哪一方
		int mySide;

		// 用于回退的log
		stack<DisappearLog> logs;

		// 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
		Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

		//!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

		// 本回合双方即将执行的动作，需要手动填入
		Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

		// 判断行为是否合法（出界或移动到非空格子算作非法）
		// 未考虑坦克是否存活
		bool ActionIsValid(int side, int tank, Action act)
		{
			if (act == Invalid)
				return false;
			if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
				return false;
			if (act == Stay || act > Left)
				return true;
			int x = tankX[side][tank] + dx[act],
				y = tankY[side][tank] + dy[act];
			return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
		}

		// 判断 nextAction 中的所有行为是否都合法
		// 忽略掉未存活的坦克
		bool ActionIsValid()
		{
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
						return false;
			return true;
		}

	private:
		void _destroyTank(int side, int tank)
		{
			tankAlive[side][tank] = false;
			tankX[side][tank] = tankY[side][tank] = -1;
		}

		void _revertTank(int side, int tank, DisappearLog& log)
		{
			int &currX = tankX[side][tank], &currY = tankY[side][tank];
			if (tankAlive[side][tank])
				gameField[currY][currX] &= ~tankItemTypes[side][tank];
			else
				tankAlive[side][tank] = true;
			currX = log.x;
			currY = log.y;
			gameField[currY][currX] |= tankItemTypes[side][tank];
		}
	public:

		// 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
		bool DoAction()
		{
			if (!ActionIsValid())
				return false;

			// 1 移动
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];

					// 保存动作
					previousActions[currentTurn][side][tank] = act;
					if (tankAlive[side][tank] && ActionIsMove(act))
					{
						int &x = tankX[side][tank], &y = tankY[side][tank];
						FieldItem &items = gameField[y][x];

						// 记录 Log
						DisappearLog log;
						log.x = x;
						log.y = y;
						log.item = tankItemTypes[side][tank];
						log.turn = currentTurn;
						logs.push(log);

						// 变更坐标
						x += dx[act];
						y += dy[act];

						// 更换标记（注意格子可能有多个坦克）
						gameField[y][x] |= log.item;
						items &= ~log.item;
					}
				}

			// 2 射♂击!
			set<DisappearLog> itemsToBeDestroyed;
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];
					if (tankAlive[side][tank] && ActionIsShoot(act))
					{
						int dir = ExtractDirectionFromAction(act);
						int x = tankX[side][tank], y = tankY[side][tank];
						bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
						while (true)
						{
							x += dx[dir];
							y += dy[dir];
							if (!CoordValid(x, y))
								break;
							FieldItem items = gameField[y][x];
							//tank will not be on water, and water will not be shot, so it can be handled as None
							if (items != None && items != Water)
							{
								// 对射判断
								if (items >= Blue0 &&
									!hasMultipleTankWithMe && !HasMultipleTank(items))
								{
									// 自己这里和射到的目标格子都只有一个坦克
									Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
									if (ActionIsShoot(theirAction) &&
										ActionDirectionIsOpposite(act, theirAction))
									{
										// 而且我方和对方的射击方向是反的
										// 那么就忽视这次射击
										break;
									}
								}

								// 标记这些物件要被摧毁了（防止重复摧毁）
								for (int mask = 1; mask <= Red1; mask <<= 1)
									if (items & mask)
									{
										DisappearLog log;
										log.x = x;
										log.y = y;
										log.item = (FieldItem)mask;
										log.turn = currentTurn;
										itemsToBeDestroyed.insert(log);
									}
								break;
							}
						}
					}
				}

			for (auto& log : itemsToBeDestroyed)
			{
				switch (log.item)
				{
				case Base:
				{
					int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
					baseAlive[side] = false;
					break;
				}
				case Blue0:
					_destroyTank(Blue, 0);
					break;
				case Blue1:
					_destroyTank(Blue, 1);
					break;
				case Red0:
					_destroyTank(Red, 0);
					break;
				case Red1:
					_destroyTank(Red, 1);
					break;
				case Steel:
					continue;
				default:
					;
				}
				gameField[log.y][log.x] &= ~log.item;
				logs.push(log);
			}

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					nextAction[side][tank] = Invalid;

			currentTurn++;
			return true;
		}


		// 回到上一回合
		bool Revert()
		{
			if (currentTurn == 1)
				return false;

			currentTurn--;
			for (int i = 0; i < 2; i++)
			{
				for (int j = 0; j < 2; j++)
				{
					nextAction[i][j] = previousActions[currentTurn][i][j];
				}
			}
			
			while (!logs.empty())
			{
				DisappearLog& log = logs.top();
				if (log.turn == currentTurn)
				{
					logs.pop();
					switch (log.item)
					{
					case Base:
					{
						int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
						baseAlive[side] = true;
						gameField[log.y][log.x] = Base;
						break;
					}
					case Brick:
						gameField[log.y][log.x] = Brick;
						break;
					case Blue0:
						_revertTank(Blue, 0, log);
						break;
					case Blue1:
						_revertTank(Blue, 1, log);
						break;
					case Red0:
						_revertTank(Red, 0, log);
						break;
					case Red1:
						_revertTank(Red, 1, log);
						break;
					default:
						;
					}
				}
				else
					break;
			}
			return true;
		}

		// 游戏是否结束？谁赢了？
		GameResult GetGameResult()
		{
			bool fail[sideCount] = {};
			for (int side = 0; side < sideCount; side++)
				if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
					fail[side] = true;
			if (fail[0] == fail[1])
				return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
			if (fail[Blue])
				return Red;
			return Blue;
		}

		/* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
		   initialize gameField[][]
		   brick>water>steel
		*/

		// 打印场地
		void DebugPrint()
		{
#ifndef _BOTZONE_ONLINE
			const string side2String[] = { "蓝", "红" };
			const string boolean2String[] = { "已炸", "存活" };
			const char* boldHR = "==============================";
			const char* slimHR = "------------------------------";
			cout << boldHR << endl
				<< "图例：" << endl
				<< ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
				<< "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
				<< slimHR << endl;
			for (int y = 0; y < fieldHeight; y++)
			{
				for (int x = 0; x < fieldWidth; x++)
				{
					switch (gameField[y][x])
					{
					case None:
						cout << '.';
						break;
					case Brick:
						cout << '#';
						break;
					case Steel:
						cout << '%';
						break;
					case Base:
						cout << '*';
						break;
					case Blue0:
						cout << 'b';
						break;
					case Blue1:
						cout << 'B';
						break;
					case Red0:
						cout << 'r';
						break;
					case Red1:
						cout << 'R';
						break;
					case Water:
						cout << 'W';
						break;
					default:
						cout << '@';
						break;
					}
				}
				cout << endl;
			}
			cout << slimHR << endl;
			for (int side = 0; side < sideCount; side++)
			{
				cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
				for (int tank = 0; tank < tankPerSide; tank++)
					cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
				cout << endl;
			}
			cout << "当前回合：" << currentTurn << "，";
			GameResult result = GetGameResult();
			if (result == -2)
				cout << "游戏尚未结束" << endl;
			else if (result == -1)
				cout << "游戏平局" << endl;
			else
				cout << side2String[result] << "方胜利" << endl;
			cout << boldHR << endl;
#endif
		}

		bool operator!= (const TankField& b) const
		{

			for (int y = 0; y < fieldHeight; y++)
				for (int x = 0; x < fieldWidth; x++)
					if (gameField[y][x] != b.gameField[y][x])
						return true;

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					if (tankX[side][tank] != b.tankX[side][tank])
						return true;
					if (tankY[side][tank] != b.tankY[side][tank])
						return true;
					if (tankAlive[side][tank] != b.tankAlive[side][tank])
						return true;
				}

			if (baseAlive[0] != b.baseAlive[0] ||
				baseAlive[1] != b.baseAlive[1])
				return true;

			if (currentTurn != b.currentTurn)
				return true;

			return false;
		}

		//构造函数
		TankField() {}
		TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide)
		{
			for (int i = 0; i < 3; i++)
			{
				int mask = 1;
				for (int y = i * 3; y < (i + 1) * 3; y++)
				{
					for (int x = 0; x < fieldWidth; x++)
					{
						if (hasBrick[i] & mask)
							gameField[y][x] = Brick;
						else if (hasWater[i] & mask)
							gameField[y][x] = Water;
						else if (hasSteel[i] & mask)
							gameField[y][x] = Steel;
						mask <<= 1;
					}
				}
			}
			for (int side = 0; side < sideCount; side++)
			{
				for (int tank = 0; tank < tankPerSide; tank++)
					gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
				gameField[baseY[side]][baseX[side]] = Base;
			}
		}
		TankField & operator =(TankField & priority)
		{
			for (int i = 0; i < fieldHeight; i++)
				for (int j = 0; j < fieldWidth; j++)
				{
					gameField[i][j] = priority.gameField[i][j];
				}
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankAlive[i][j] = priority.tankAlive[i][j];
			for (int i = 0; i < sideCount; i++)
				baseAlive[i] = priority.baseAlive[i];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankX[i][j] = priority.tankX[i][j];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankY[i][j] = priority.tankY[i][j];
			currentTurn = priority.currentTurn;
			mySide = priority.mySide;
			logs = priority.logs;
			for (int i = 0; i < 101; i++)
				for (int j = 0; j < sideCount; j++)
					for (int k = 0; k < tankPerSide; k++)
						previousActions[i][j][k] = priority.previousActions[i][j][k];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					nextAction[i][j] = priority.nextAction[i][j];
			return *this;
		}
		TankField(TankField& priority)
		{
			for (int i = 0; i < fieldHeight; i++)
				for (int j = 0; j < fieldWidth; j++)
				{
					gameField[i][j] = priority.gameField[i][j];
				}
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankAlive[i][j] = priority.tankAlive[i][j];
			for (int i = 0; i < sideCount; i++)
				baseAlive[i] = priority.baseAlive[i];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankX[i][j] = priority.tankX[i][j];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankY[i][j] = priority.tankY[i][j];
			currentTurn = priority.currentTurn;
			mySide = priority.mySide;
			logs = priority.logs;
			for (int i = 0; i < 101; i++)
				for (int j = 0; j < sideCount; j++)
					for (int k = 0; k < tankPerSide; k++)
						previousActions[i][j][k] = priority.previousActions[i][j][k];
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					nextAction[i][j] = priority.nextAction[i][j];
		}
		TankField(FieldItem GameField[9][9], int myside = 0)
		{
			for (int i = 0; i < fieldHeight; i++)
				for (int j = 0; j < fieldWidth; j++)
				{
					if (GameField[i][j] <= 4 || GameField[i][j] == Water)
						gameField[i][j] = GameField[i][j];
					else
						gameField[i][j] = None;
				}
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					tankAlive[i][j] = false;
			for (int i = 0; i < sideCount; i++)
				baseAlive[i] = true;

			currentTurn = 2;
			mySide = myside;
			for (int j = 0; j < sideCount; j++)
				for (int k = 0; k < tankPerSide; k++)
					previousActions[0][j][k] = Stay;
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
					nextAction[i][j] = Stay;
			for (int i = 0; i < sideCount; i++)
				for (int j = 0; j < tankPerSide; j++)
				{
					tankX[i][j] = -1;
					tankY[i][j] = -1;
				}
		}


};

#ifdef _MSC_VER
#pragma endregion
#endif

	TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

	// 内部函数
	namespace Internals
	{
		Json::Reader reader;
#ifdef _BOTZONE_ONLINE
		Json::FastWriter writer;
#else
		Json::StyledWriter writer;
#endif

		void _processRequestOrResponse(Json::Value& value, bool isOpponent)
		{
			if (value.isArray())
			{
				if (!isOpponent)
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
				}
				else
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
					field->DoAction();
				}
			}
			else
			{
				// 是第一回合，裁判在介绍场地
				int hasBrick[3], hasWater[3], hasSteel[3];
				for (int i = 0; i < 3; i++) {//Tank2 feature(???????????????)
					hasWater[i] = value["waterfield"][i].asInt();
					hasBrick[i] = value["brickfield"][i].asInt();
					hasSteel[i] = value["steelfield"][i].asInt();
				}
				field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
			}
		}

		// 请使用 SubmitAndExit 或者 SubmitAndDontExit
		void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
		{
			Json::Value output(Json::objectValue), response(Json::arrayValue);
			response[0U] = tank0;
			response[1U] = tank1;
			output["response"] = response;
			if (!debug.empty())
				output["debug"] = debug;
			if (!data.empty())
				output["data"] = data;
			if (!globalData.empty())
				output["globalData"] = globalData;
			cout << writer.write(output) << endl;
		}
	}

	// 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
	// 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
	void ReadInput(istream& in, string& outData, string& outGlobalData)
	{
		Json::Value input;
		string inputString;
		do
		{
			getline(in, inputString);
		} while (inputString.empty());
#ifndef _BOTZONE_ONLINE
		// 猜测是单行还是多行
		char lastChar = inputString[inputString.size() - 1];
		if (lastChar != '}' && lastChar != ']')
		{
			// 第一行不以}或]结尾，猜测是多行
			string newString;
			do
			{
				getline(in, newString);
				inputString += newString;
			} while (newString != "}" && newString != "]");
		}
#endif
		Internals::reader.parse(inputString, input);

		if (input.isObject())
		{
			Json::Value requests = input["requests"], responses = input["responses"];
			if (!requests.isNull() && requests.isArray())
			{
				size_t i, n = requests.size();
				for (i = 0; i < n; i++)
				{
					Internals::_processRequestOrResponse(requests[i], true);
					if (i < n - 1)
						Internals::_processRequestOrResponse(responses[i], false);
				}
				outData = input["data"].asString();
				outGlobalData = input["globaldata"].asString();
				return;
			}
		}
		Internals::_processRequestOrResponse(input, true);
	}

	// 提交决策并退出，下回合时会重新运行程序
	void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
	{
		Internals::_submitAction(tank0, tank1, debug, data, globalData);
		exit(0);
	}

	// 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
	// 如果游戏结束，程序会被系统杀死
	void SubmitAndDontExit(Action tank0, Action tank1)
	{
		Internals::_submitAction(tank0, tank1);
		field->nextAction[field->mySide][0] = tank0;
		field->nextAction[field->mySide][1] = tank1;
		cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
	}
#ifdef _MSC_VER
#pragma endregion
#endif
}
int RandBetween(int from, int to)
{
	return rand() % (to - from) + from;
}

TankGame::Action RandAction(int tank)
{
	while (true)
	{
		auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
		if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
			return act;
	}
}
using namespace TankGame;

//超参数
struct Sparameterlist
{
	//全局参数
	double rusher;//表示在稳定盘面上冒着死亡风险冲过去的概率
	double lessen;//回合间传参递减
	int runtime;//表示一次evaluate的用时
	int givetime;//表示给定的上限时间,应当是1s
	double alpha;//表示ab剪枝率
	int open_dimension;//表示评估矩阵的展开系数
	int open_layer;//表示可以展开的层数，通过计算得到，0表示未计算
	bool emergency;
	//注意，第一层为layer = 1；

	double killtank;
	double bekilltank;
	double roadcontrol;//表示对一条路控制力改变的衡量
	double movedelta;//表示最小到达的参数衡量
	double limitation;//表示超过多少的时候选取
	double shootdanger;//表示射击的潜在风险
	Sparameterlist()//构造函数，值初始化
	{
		rusher = 0.3333;
		emergency = false;
		lessen = 0.7;
		runtime = open_layer = 0;
		open_dimension = 3; givetime = 1000; alpha = 1;
		killtank = bekilltank = 30;
		roadcontrol = 6;
		movedelta = 4;
		//limitation = 1.3;
		shootdanger = 10;
	}
}paralist;

using namespace std;
struct outtempstore
{
	double value;
	double meaninside;
	int myaction;
	vector<int> ac;
	vector<double> eachvalue;
	friend bool operator < (outtempstore const & a,outtempstore const & b)
	{
		return a.meaninside > b.meaninside;
	}
	outtempstore()
	{
		value = meaninside = 0;
		ac.clear(); eachvalue.clear();
	}
};

//评估层之间的传参列表
struct returnstruct
{
	Action bestac[2];
	double value = -10000;
	returnstruct()
	{
		value = -10000;
		for (int i = 0; i < 2; i++)
		{
			for (int j = 0; j < 2; j++)
				bestac[i] = Stay;
		}
	}
};

struct tempstore
{
	double value;
	int number;
	tempstore() :value(0), number(0) {}
	friend bool operator < (tempstore const & a, tempstore const & b)
	{
		return a.value < b.value;
	}
};
//与盘面（土块变化）无关的所有数据
struct overview
{
	bool havecalculate;//表示是否已经计算过
	int path;//表示对方能到达的路径数量
	bool unlose_probability;//表示每条路径都存在理论防守位置（1对1）的发生与否
	std::vector<int> unbeaten[4];//记录理论防守点的位置,有多个则push_back
	int road[4]; //0表示双开 1表示侧面开 2表示中间开
	TankField *unmove;
	int arrivefield[2][9][9];

	overview()
	{
		havecalculate = false;
		path = -1;
		unlose_probability = false;
		for (int i = 0; i < 4; i++)
			unbeaten[i].clear(), road[i] = 1;
		
	}
}view;


//对于一个盘面的所有操作得到的一个类
class accessfield
{
public:
	struct bfs_direction
	{
		int x, y;
		int foot;//表示这个位置的步数，用于广搜传参
		bfs_direction(int xx, int yy, int tempfoot) :x(xx), y(yy), foot(tempfoot) {}
		bfs_direction(int k)
		{
			foot = 0;
			if (k == 0)x = 0, y = -1;
			else if (k == 1)x = 1, y = 0;
			else if (k == 2)x = 0, y = 1;
			else x = -1, y = 0;
		}
	}dir[4] = { 0,1,2,3 };
	struct footrun
	{
		int x, y;
	}direction[4] = { {0,-1},{1,0},{0,1},{-1,0} };
	struct unchangestruct//表示对这个盘面不变的所有量
	{
		int nummy, numen;
		TankField *origin;//表示不带行动的原始棋盘
		int ori_arrivefield[2][9][9];//表示原始棋盘的刺杀最小步数
		TankField *save;
		int save_arrivefield[2][9][9];//表示不带土块的每个位置刺杀所需要的最小步数
		int arrivefield[81][2][9][9];//表示双方对应操作i后每个位置刺杀所需要的最小步数
		int thwartroad[81][2][9][9];//表示我方的移动是否使得对方突然更好（让开路）
		int dencemin[4][12][9][9];//表示4条路径上，至多10个的理论防守点中，side的最小步数
		int roaddefence[2][4]; //表示是否我到4条路的最优的理论防守位置都比他好
		int roadimportance[2][2];//表示side放两侧的重要路径是0（mid）还是1（边）
		unchangestruct()
		{
			nummy = numen = 0;
		}
	}unchange;

	
	//对 sizen * sizem个盘面，每个盘面对应一个changestruct，记录估值、是否选取、死亡情况等seperate situation
	struct changestruct
	{
		bool choose;
		double value;//表示综合性的估值
		int delta_minarrive[2][2];//表示每边坦克最小到达步数的改变情况,负的表示好的
		int delta_numtank[2];//表示每边tank数量的变化
		bool basedeath[2];//表示这个操作是否出现了刺杀对方基地的情况
		int roaddefence[2][4];//同unchange里面的
		bool tankdeath[2][2];//表示tank是否死亡
		int shootdanger;//表示射击是否危险
		int whoiscloser[2];//值为side，表示左侧和右侧（0,1）是side离杀死对方更接近
		//构造函数
		changestruct()
		{
			shootdanger = 0;
			choose = false; value = 0;
			for (int side = 0; side < 2; side++)
			{
				tankdeath[side][0] = tankdeath[side][1] = false;
				delta_minarrive[side][0] = delta_minarrive[side][1] = delta_numtank[side] = basedeath[side] = 0;
				for (int j = 0; j < 4; j++)
				{
					roaddefence[side][j] = -100;
				}
			}
		}
	};
	//int arrive_step[2][2];//表示tank射杀对方基地需要的最小步数

	//广搜的最短路
	struct bfs
	{
		int x;
		int y;
		int foot;
		bfs(int xx, int yy, int  ffoot) :x(xx), y(yy), foot(ffoot) {}
		friend bool operator < (const bfs & a, const bfs & b)
		{
			return a.foot > b.foot;
		}
	};

	//最短路，判断到达位置A的最小距离
	void arrive_min(TankField *p, int px, int py, int minfield[9][9], int calside = -1)
	{
		TankField &cur = *p;
		for (int x = 0; x < fieldHeight; x++)
		{
			for (int y = 0; y < fieldWidth; y++)
			{
				if (view.unmove->gameField[y][x] != None) minfield[y][x] = -1;
				else minfield[y][x] = -2;
			}
		}
		minfield[py][px] = 0;

		priority_queue<bfs> a;
		bfs temp(px, py, 0); a.push(temp);
		while (!a.empty())
		{
			bfs t = a.top(); a.pop();
			for (int orr = 0; orr < 4; orr++)
			{
				int xx = t.x + direction[orr].x, yy = t.y + direction[orr].y;
				if (!CoordValid(xx, yy))continue;
				if (minfield[yy][xx] == -1)continue;//表示这个位置不可到达
				int k = 1;
				if (unchange.origin->gameField[t.y][t.x] == Brick)k++;
				if (minfield[yy][xx] < 0)
				{
					bfs add(xx, yy, t.foot + k);
					minfield[yy][xx] = t.foot + k;
					a.push(add);
				}
			}
		}
	}
	/*
	void arrive_min(TankField *p, int px, int py, int minfield[9][9], int calside = -1)
	{
		TankField & cur = *p;

		//不能到达的区域标记
		for (int x = 0; x < fieldWidth; x++)
		{
			for (int y = 0; y < fieldHeight; y++)
			{
				if (view.unmove->gameField[y][x] != None)
					minfield[y][x] = minfield[y][x] = -1;
				else
					minfield[y][x] = minfield[y][x] = -2;
			}
		}

		minfield[py][px] = minfield[py][px] = 0;


		int a[200][3]; memset(a, -1, sizeof(a)); int l = 0, r = 0;
		a[r][0] = px, a[r][1] = py, a[r++][2] = 0;
		while (r != l)
		{
			int tx = a[l][0], ty = a[l][1], foot = a[l][2]; l++;
			for (int orr = 0; orr < 4; orr++)
			{
				int xx = tx + direction[orr].x, yy = ty + direction[orr].y;
				if (!CoordValid(xx, yy))continue;
				if (minfield[yy][xx] == -1)continue;//表示这个位置不可到达
				int k = 1;
				if (unchange.origin->gameField[ty][tx] == Brick)k++;
				if (minfield[yy][xx] < 0 || minfield[yy][xx] > foot + k)
				{
					a[r][0] = xx; a[r][1] = yy;

					minfield[yy][xx] = a[r++][2] = foot + k;
				}
			}

		}


	}
	*/
	
	//全图不同位置射杀对方基地所需要的步数的最小值
	void arrive_calculation(const TankField * p, int arrivefield[2][9][9], int calside = -1,int caltank = 0)
	{
		TankField const & cur = *p;
		//对双方进行地图标记


		//可到达区域标记
		for (int side = 0; side < sideCount; side++)
		{
			if (calside == 0 && side == 1)continue;
			if (calside == 1 && side == 0)continue;
			//不能到达区域标记
			for (int x = 0; x < fieldWidth; x++)
			{
				for (int y = 0; y < fieldHeight; y++)
				{
					if (cur.gameField[y][x] == Steel || cur.gameField[y][x] == Water || cur.gameField[y][x] == Base)
						arrivefield[side][y][x] = -1;
					else
						arrivefield[side][y][x] = -2;
					if (caltank != 0)
					{
						for (int j = 0; j < 2; j++)
						{
							if (!cur.tankAlive[1 - side][j])continue;
							if (cur.tankX[1 - side][j] == x && cur.tankY[1 - side][j] == y)
							{
								if (!HasMultipleTank(cur.gameField[y][x]))
									arrivefield[side][y][x] = -1;
							}
						}
					}
				}
			}

			queue<bfs_direction> q[7];//到达步数阵列，q[0]不使用
			int maxquse = 0;

			//对和基地共线的部分进行标记
			int run[3][2] = { 1,0,-1,0,0,-1 };
			if (side == 1)run[2][1] = 1;//如果是红色改为向下

			//标记的搜索循环if(
			for (int orretation = 0; orretation < 3; orretation++)
			{
				int x = baseX[1 - side], y = baseY[1 - side];
				x += run[orretation][0], y += run[orretation][1];
				int tempfoot = 0;
				while (CoordValid(x, y))
				{
					if (cur.gameField[y][x] == Steel)break;
					else if (cur.gameField[y][x] == Water)
					{
						x += run[orretation][0], y += run[orretation][1];
						continue;
					}
					else
					{
						if (tempfoot == 0)
						{
							arrivefield[side][y][x] = tempfoot = 1;
							q[1].push(bfs_direction(x, y, tempfoot));
							maxquse = std::max(maxquse, tempfoot);
						}
						else
						{
							int tx = x - run[orretation][0], ty = y - run[orretation][1];

							if (cur.gameField[ty][tx] == Brick)//需要摧毁的
								tempfoot += 2;
							arrivefield[side][y][x] = tempfoot;
							q[tempfoot].push(bfs_direction(x, y, tempfoot));
							maxquse = std::max(maxquse, tempfoot);
						}
						x += run[orretation][0], y += run[orretation][1];
					}
				}
			}

			//其余部分标记 广搜
			for (int i = 1; i <= maxquse; i++)
			{
				while (!q[i].empty())
				{
					bfs_direction pre = q[i].front();
					q[i].pop();
					int x = pre.x, y = pre.y;
					if (arrivefield[side][y][x] != -2 && pre.foot > arrivefield[side][y][x])continue;//已经被算过，之前算的步数不超过之后算的，所以跳过
					int adder = 1 + (cur.gameField[y][x] == Brick);
					int spillfoot = pre.foot + adder;
					for (int j = 0; j < 4; j++)
					{
						int xx = x + dir[j].x, yy = y + dir[j].y;
						if (CoordValid(xx, yy))
						{
							if (arrivefield[side][yy][xx] == -2 || spillfoot < arrivefield[side][yy][xx])
							{
								arrivefield[side][yy][xx] = spillfoot;
								q[std::min(spillfoot, maxquse)].push(bfs_direction(xx, yy, spillfoot));
							}
						}
					}
				}
			}
		}
		//至此，对arrivefield的标记完成
		
		
	}

	//计算存在路数 2 或 4,和理论防守位置，全局不变
	void road_initialization(FieldItem gamefield[9][9], const int arrivefield[2][9][9],int &path,int road[4])
	{
		path = 4;//总路径
		road[0] = road[1] = road[2] = road[3] = 1;

		//判读中路到达情况
		for (int j = 0; j < 2; j++)
		{
			int p;
			switch (j)
			{
			case 0:p = 3; break;
			case 1:p = 5; break;
			}
			for (int side = 0; side < 2; side++)
			{
				int k = (side == 0) ? 1 : -1;
				if (arrivefield[side][4][p] > arrivefield[side][4 - k][p] || arrivefield[side][4][p] < 0)
				{
					path--;
					road[j + 1] = 0;
					break;
				}
			}
		}

	

		//判断边路到达情况
		for (int side = 0; side < 2; side++)
		{
			int k = (side == 0) ? 1 : -1;
			if ((arrivefield[side][4][0] > arrivefield[side][4 - k][0]||arrivefield[side][4][0] <0) && (arrivefield[side][4][1] > arrivefield[side][4 - k][1] || arrivefield[side][4][1] < 0))
			{
				path --; 
				road[0] = 0;
				break;
			}
		}
		for (int side = 0; side < 2; side++)
		{
			int k = (side == 0) ? 1 : -1;
			if ((arrivefield[side][4][7] > arrivefield[side][4 - k][7] || arrivefield[side][4][7] < 0) && (arrivefield[side][4][8] > arrivefield[side][4 - k][8] || arrivefield[side][4][8] < 0))
			{
				path --; 
				road[3] = 0; 
				break;
			}
		}


	}

	//计算理论防御点
	void theoreticaldefence(int debugging = 0)
	{
		int temparrivefield[2][9][9];
		int temppath, temproad[4];
		TankField * temp = new TankField(view.unmove->gameField); //初始化地盘
		for (int x = 0; x < 9; x++)
		{
			for (int y = 0; y < 9; y++)
			{
				if (x == 5 && y == 8)
					x = x;
				if (view.unmove->gameField[y][x] != None)continue;//因为给进来的initialization一定是一个只有none和unmove的情况
				//FieldItem store = view.unmove->gameField[y][x];
				//view.unmove->gameField[y][x] = Steel;
				FieldItem store = temp->gameField[y][x];
				temp->gameField[y][x] = Steel;
				//TankField *temp = new TankField(view.unmove->gameField);
				arrive_calculation(temp, temparrivefield);
				road_initialization(temp->gameField, temparrivefield, temppath, temproad);
				for (int i = 0; i < 4; i++)
				{
					if (temproad[i] != view.road[i])//表示这个使得这条路径被封死
					{
						view.unbeaten[i].push_back(9 * x + y);
					}
				}

				//回溯
				temp->gameField[y][x] = store;
				//view.unmove->gameField[y][x] = store;

			}
		}

	}
	

	void road_importance(TankField *ptr, int roadimp[2][2])
	{
		int temparrivefield[2][9][9];
		TankField * temp = new TankField(*ptr);
		for (int side = 0; side < 2; side++)
		{
			for (int j = 0; j < 2; j++)
			{
				int p = (side == j) ? 3 : 5;
				if (!ptr->tankAlive[side][j]) { roadimp[side][j] = -1; continue; }
				FieldItem store = temp->gameField[4][p];
				temp->gameField[4][p] = Steel;
				//操作
				arrive_calculation(temp, temparrivefield, side);
				int x = temp->tankX[side][j], y = temp->tankY[side][j];
				if (temparrivefield[side][y][x] != unchange.ori_arrivefield[side][y][x])//表示这个操作使得值变了，一定是变大了，说明中路是主要路径
					roadimp[side][j] = 0;
				else
					roadimp[side][j] = 1;

				//回溯
				temp->gameField[4][p] = store;
			}
		}

	}

	//计算理论防守点的广搜图
	void defence_graph_calculation(TankField *ptr,int dencemin[4][12][9][9],int calside = -1)
	{
		for (int road = 0; road < 4; road++)
		{
			if (view.road[road] == 0)continue;
			for (int po = 0; po < (int)view.unbeaten[road].size(); po++)
				arrive_min(ptr, view.unbeaten[road][po] / 9, view.unbeaten[road][po] % 9, dencemin[road][po]);
		}
	}


	//计算防守情况
	void denfencecalculation(int roader[2][4], TankField *cur, int dencemin[4][12][9][9], Action ac[2][2])
	{
		//标注：cur是已经执行完的盘面 ac里面存了这回合的两个行动 dencemin是origin的最短路广搜
		for (int road = 0; road < 4; road++)
		{
			if (view.road[road] == 0)continue;
			int lorr = 0;
			if (road >= 2)lorr = 1;
			if (cur->tankY[0][lorr] > cur->tankY[1][1 - lorr])
			{
				
				roader[0][road] = -100;
				roader[1][road] = -100;
				continue;
			}
			for (int side = 0; side < 2; side++)
			{
				roader[side][road] = -100;
				for (int po = 0; po < (int)view.unbeaten[road].size(); po++)
				{
					//首先判断这个点是否确实能成为防守点 判断方法是如果这个点的arrivemin比actually的arrivemin要大，那么认为就不行
					
					int minn[2] = { 100,100 };//表示双方到达这个点的步数最小值
					int tempj = (road < 2) ? 1 - side : side;
					int ty = cur->tankY[1 - side][tempj];
					int py = view.unbeaten[road][po] % 9;
					if (cur->tankAlive[1 - side][tempj])
					{
						if ((ty < py && side == 0) || (ty > py && side == 1))
							continue;
					}

					for (int i = 0; i < 2; i++)
					{

						for (int j = 0; j < 2; j++)
						{
							if (!cur->tankAlive[i][j])continue;//如果这个tank已经死亡
							int temper = 0;//表示这个tank到这个点的距离

							//计算距离的模块
							int x = cur->tankX[i][j], y = cur->tankY[i][j];
							temper = dencemin[road][po][y][x];
							if (ac[i][j] >= UpShoot)//不是移动，那么位置不变
							{
								int orr = ac[i][j] - UpShoot;//↑→↓←分别为0123
								int xx = x + direction[orr].x, yy = y + direction[orr].y;
								if (CoordValid(xx, yy))
								{
									if (dencemin[road][po][yy][xx] == -1)temper++;
									else
									{
										int delta = dencemin[road][po][yy][xx] - temper;
										if (delta >= 0)
											temper++;
										else if (delta == -2)//如果是-2的话就射的很对
											temper--;
										else //这个时候只能是-1了
										{
											if (unchange.origin->gameField[yy][xx] == Brick)//被射击的位置是土块，差为-1,说明这一条不是最优路径
												temper++;
											else//判断这个方向是不是是最佳路径
											{
												int flag = 0;
												int tx = xx, ty = yy;
												while (true)
												{
													xx = tx, yy = ty;
													tx += direction[orr].x, ty += direction[orr].y;
													if (!CoordValid(tx, ty))
														break;
													if (dencemin[road][po][ty][tx] - dencemin[road][po][yy][xx] == -2)
													{
														flag = 1; break;
													}
													else if (dencemin[road][po][ty][tx] - dencemin[road][po][yy][xx] >= 0)
														break;
												}
												if (flag == 0)temper++;
												else temper--;
											}
										}
									}
									
								}
								else
									temper++;
							}
		



							minn[i] = std::min(temper, minn[i]);
						}
					}
					if (minn[0] == 100 || minn[1] == 100)//表示根本没有参与 计算 tank双死亡
						roader[side][road] = -100;
					else
						roader[side][road] = std::max(roader[side][road], minn[1 - side] - minn[side]);
				}
			}
		}
	}


	//void denfencecalculation(int roader[2][4], TankField * cur, int dencemin[4][10][9][9], int endencemin[4][10][9][9],int different = 0)
	
	//表示没有行动的盘面的测算（就是origin的）
	void denfencecalculation(int roader[2][4],TankField * cur,int dencemin[4][12][9][9])
	{
		for (int road = 0; road < 4; road++)
		{

			if (view.road[road] == 0)continue;
			//if(different == 0)
			
			for (int side = 0; side < 2; side++)
			{
				roader[side][road] = -100;
				for (int po = 0; po < (int)view.unbeaten[road].size(); po++)
				{
					int minn[2] = { 100,100 };//表示双方到这个点的步数最小值
					for (int i = 0; i < 2; i++)
					{
						for (int j = 0; j < 2; j++)
						{
							if (!cur->tankAlive[i][j])continue;
							int temper = dencemin[road][po][cur->tankY[i][j]][cur->tankX[i][j]];
							if (cur->currentTurn > 1 )
								if (cur->previousActions[cur->currentTurn - 1][i][j] > 3)//射击操作
									if (temper == unchange.dencemin[road][po][cur->tankY[i][j]][cur->tankX[i][j]])
									{
										int flag = 1;
										for (int orr = 0; orr < 4; orr++)
										{
											int xx = cur->tankX[i][j] + direction[orr].x, yy = cur->tankY[i][j] + direction[orr].y;
											if (CoordValid(xx, yy))
												if (dencemin[road][po][yy][xx] != -1)
													if (temper - dencemin[road][po][yy][xx] == 1)
													{
														flag = 0;
														break;
													}
										}
										if (flag)temper++;
									}
							minn[i] = std::min(temper, minn[i]);
						}
					}
					roader[side][road] = std::max(roader[side][road], minn[1 - side] - minn[side]);
				}
			}
			
		}

	}

	double sigmoid(int k)
	{
		//return 1;	
		int fuhao = 1;
		if (k == 0)return 1;
		if (k < 0)fuhao = -1, k = -k;
		double s = (double) 1 / (1 + log(k));
		return s ;
	}

	//接口函数，承担class初始化、子函数调用、返回值的utility
	//template<int sizen,int sizem>
//#define sizen 5
//#define sizem 3
	priority_queue<outtempstore> DoEvaluate(TankField ptrcur,vector<pair<Action,Action> > aclist[2],int layer)
	{
		int myside = ptrcur.mySide;
		//debugging = 1;
		int sizen = aclist[myside].size(), sizem = aclist[1 - myside].size();

		changestruct **change;
		change = new changestruct *[sizen];
		for (int my = 0; my < sizen; my++)
			change[my] = new changestruct[sizem];
		unchange.origin = new TankField(ptrcur);
		for (int i = 0; i < 2; i++)for (int j = 0; j < 2; j++)	unchange.origin->nextAction[i][j] = Stay;
		unchange.save = new TankField(ptrcur.gameField, ptrcur.mySide);
		unchange.nummy = sizen, unchange.numen = sizem;

		arrive_calculation(unchange.origin, unchange.ori_arrivefield);
		timelog[clock_num++] = clock();

		//首先进行不改变的量的计算
		if (view.havecalculate == false)
		{
			clock_t start = clock();
			view.havecalculate = true;
			FieldItem unmove[9][9];
			for (int x = 0; x < 9; x++)
			{
				for (int y = 0; y < 9; y++)
				{
					if (unchange.save->gameField[y][x] != Water && unchange.save->gameField[y][x] != Steel && unchange.save->gameField[y][x] != Base)
						unmove[y][x] = None;
					else
						unmove[y][x] = unchange.save->gameField[y][x];
				}
			}
			
			view.unmove = new TankField(unmove, 0);
			//view.unmove->DebugPrint();
			
			arrive_calculation(view.unmove, view.arrivefield);
			road_initialization(view.unmove->gameField, view.arrivefield, view.path, view.road);
			theoreticaldefence();
			//clock_t end = clock() - start;
			//cout << end << endl;
		}
		timelog[clock_num++] = clock();
		viewtime = clock_num - 1;
		//cout << "viewtime" << viewtime << endl;
		//接下来是unbeaten的初始化
		defence_graph_calculation(unchange.origin, unchange.dencemin);
		
		//cout << "所有理论防守点的计算耗时为" << ender << endl;
		denfencecalculation(unchange.roaddefence, unchange.origin,unchange.dencemin);

		//进行路径重要性的计算
		road_importance(unchange.origin, unchange.roadimportance);

		//是否冒险的判定
		bool adventure = false;
		srand((unsigned)time(NULL));
		int delta = rand() % 10;
		for (int i = 0; i < delta; i++)
			rand();
		double trynum = ( rand() % 1000 )/ (float)1000;
		if (trynum < paralist.rusher &&layer == 1)
			trynum = trynum;
		//trynum = 0;//不发生
		if (ptrcur.currentTurn >= 10)
		{
			bool flag = true;
			for (int i = 0; i < 3; i++)
			{
				for (int side = 0; side < 2; side++)
					for (int j = 0; j < 2; j++)
						if ((ptrcur.previousActions[ptrcur.currentTurn - 1 - i][side][j] != ptrcur.previousActions[ptrcur.currentTurn - 1][side][j]))
						{
							flag = false;
							break;
						}
			}
			if (flag == true)
				adventure = true;
		}
		if (layer != 1)
			adventure = false;

		//接下来对所有与单方操作无关的量计算

		//合法化操作列表
		ptrcur.nextAction[0][0] = ptrcur.nextAction[0][1] = Stay;
		ptrcur.nextAction[1][0] = ptrcur.nextAction[1][1] = Stay;

		ptrcur.DoAction();
		int a = 0;
		ptrcur.Revert();

		for (int side = 0; side < 2; side++)
		{
			TankField temp = ptrcur;
			int numaction = (side == unchange.save->mySide) ? unchange.nummy : unchange.numen;
			for (int i = 0; i < numaction; i++)
			{
				if (side == 0 && i == 5)
					i = i;
				temp.nextAction[side][0] = aclist[side][i].first, temp.nextAction[side][1] = aclist[side][i].second;
				temp.nextAction[1 - side][0] = temp.nextAction[1 - side][1] = Stay;
				temp.DoAction();
				arrive_calculation(&temp, unchange.arrivefield[i], side);
				//arrive_calculation(&temp, unchange.thwartroad[i],1 - side,1);//记录我方操作使得对方的到达情况
				temp.Revert();
			}
		}

		timelog[clock_num++] = clock();
		
	

		//下面是针对每一个操作都不同的数值的分析，完成后给出排序
		for (int my = 0; my < unchange.nummy; my++)
		{
			for (int en = 0; en < unchange.numen; en++)
			{
				Action actemp[2][2];
				actemp[myside][0] = aclist[myside][my].first, actemp[myside][1] = aclist[myside][my].second;
				actemp[1 - myside][0] = aclist[1 - myside][en].first, actemp[1 - myside][1] = aclist[1 - myside][en].second;

				if (my == 6 && en == 0)
				{
					my = my;
				}
				for (int i = 0; i < 2; i++)
					for (int j = 0; j < 2; j++)
						ptrcur.nextAction[i][j] = actemp[i][j];

				//首先补充判断有没有进行"让路操作"
				for (int side = 0; side < 2; side++)
				{
					for (int j = 0; j < 2; j++)
					{
						//if(tank)
						//if(unchange.save_arrivefield[side][])
					}
				}

				ptrcur.DoAction();
				change[my][en].whoiscloser[0] = change[my][en].whoiscloser[1] = 0;
				for (int side = 0; side < 2; side++)
				{
					change[my][en].delta_numtank[side] = unchange.origin->tankAlive[side][0] + unchange.origin->tankAlive[side][1];
					change[my][en].delta_numtank[side] -= (ptrcur.tankAlive[side][0] + ptrcur.tankAlive[side][1]);
					change[my][en].basedeath[side] = !ptrcur.baseAlive[side];
					//存入arrive_step




					for (int j = 0; j < 2; j++)
					{
						change[my][en].tankdeath[side][j] = (bool)!ptrcur.tankAlive[side][j];
						int rowc = (side == myside) ? my : en;
						int xx = unchange.origin->tankX[side][j], yy = unchange.origin->tankY[side][j];
						int x = ptrcur.tankX[side][j], y = ptrcur.tankY[side][j];
						//用于whoiscloser计算
						int place = (side == j) ? 0 : 1;
						int qq = (side == 0) ? 1 : -1;
						if (actemp[side][j] <= 3)//表示是移动或不动
						{
							change[my][en].delta_minarrive[side][j] = -unchange.ori_arrivefield[side][yy][xx] + unchange.arrivefield[rowc][side][y][x];
							change[my][en].whoiscloser[place] += qq * unchange.arrivefield[rowc][side][y][x];
						}
						else//表示是射击
						{
							change[my][en].delta_minarrive[side][j] = unchange.arrivefield[rowc][side][y][x] - unchange.ori_arrivefield[side][yy][xx];
							change[my][en].whoiscloser[place] += qq * unchange.arrivefield[rowc][side][y][x];
							if (change[my][en].delta_minarrive[side][j] == 0)//表示这个射击并没有使得自己的步数减少,那么由于进行了一次射击：
								change[my][en].delta_minarrive[side][j]++, change[my][en].whoiscloser[place] += qq;
						}
					}
					//进行理论防守状态的计算

				}
				for (int place = 0; place < 2; place++)
				{
					if (change[my][en].whoiscloser[place] > 0)change[my][en].whoiscloser[place] = 1;
					else if (change[my][en].whoiscloser[place] < 0)change[my][en].whoiscloser[place] = 0;
					else change[my][en].whoiscloser[place] = -1;
				}
		
				denfencecalculation(change[my][en].roaddefence, &ptrcur, unchange.dencemin, actemp);

				//理论防守补充性处理
				


				//射击风险估值
				for (int side = 0; side < 2; side++)
				{
					for (int j = 0; j < 2; j++)
					{
						if (change[my][en].tankdeath[side][j])continue;
						if (ActionIsShoot(actemp[side][j]))//这是一个射击行动 防止射击后被敌人杀死
						{
							int orr = actemp[side][j] - UpShoot;
							//如果这个方向上敌人也在 并且一马平川
							for (int ent = 0; ent < 2; ent++)
							{
								if (change[my][en].tankdeath[1 - side][ent])continue;
								int dx = ptrcur.tankX[1 - side][ent] - ptrcur.tankX[side][j], dy = ptrcur.tankY[1 - side][ent] - ptrcur.tankY[side][j];
								if (dx * dy != 0)continue;
								//不可能重叠
								if (ActionIsShoot(actemp[1 - side][ent]))continue;
								if ((orr == 0 && dy < 0) || (orr == 1 && dx > 0) || (orr == 2 && dy > 0) || (orr == 3 && dx < 0))//触发了射杀危险
								{
									int flag = 1;
									for (int step = 1; step < abs(dx+dy); step++)
									{
										if (ptrcur.gameField[ptrcur.tankY[side][j] + step * direction[orr].y][ptrcur.tankX[side][j] + step * direction[orr].x] != None)
										{
											flag = 0; continue;
										}
									}
									if (flag)change[my][en].shootdanger += (side == myside) ? -1 : 1;
								}
							}
						}
					}
				}

				ptrcur.Revert();
				if (debugging)
				{
					int outer = (ptrcur.nextAction[myside][0] + 2) * 1000 + (ptrcur.nextAction[myside][1] + 2) * 100 + (ptrcur.nextAction[1-myside][0] + 2) * 10 + (ptrcur.nextAction[1-myside][1] + 2);
					//cout << std::setw(5) << outer;
				}
			}
			if (debugging)cout << endl << endl;
		}

		timelog[clock_num++] = clock();
		
		//下面进行估值

		std::pair<int, double> ** choosemartix;
		choosemartix = new std::pair<int,double>*[unchange.nummy];
		double totalvalue = 0;
		double maxvalue = -100, minvalue = 100;
		
		priority_queue<outtempstore> chooser;
		for (int my = 0; my < unchange.nummy; my++)
		{
			priority_queue<tempstore> lowvalue;
			choosemartix[my] = new std::pair<int,double>[unchange.numen];
			for (int en = 0; en < unchange.numen; en++)
			{
				if (my == 48 && en == 1)
					my = my;
				choosemartix[my][en].first = 0, choosemartix[my][en].second = 0;
				//对于每个changestruct，给一个k的返回
				double tempvalue = 0;
				if (change[my][en].basedeath[1 - myside])choosemartix[my][en].second += 100;
				if (change[my][en].basedeath[myside])choosemartix[my][en].second -= 50;
					choosemartix[my][en].second += (change[my][en].delta_numtank[1 - myside] - change[my][en].delta_numtank[myside]) * paralist.killtank;
				if(adventure == true)//认为可以考虑进行一下冒险行为,原因是对方三回合内行动都不变
				{
					if (change[my][en].delta_numtank[myside] != 0)//并且这是一个冒险行动
					{	
						if (trynum < paralist.rusher)//认为随机成功
						{
							choosemartix[my][en].second += change[my][en].delta_numtank[myside] * paralist.killtank;
							//跳过对方的射击致死操作
							continue;
						}
							//trynum = trynum;
					}
				}

				choosemartix[my][en].second += change[my][en].shootdanger * paralist.shootdanger;
			
				if (layer == 2 && my == 22 && en == 29)
					layer = layer;

				for (int side = 0; side < 2; side++)
				{
					//理论防守点估值
					int qq = (side == myside) ? 1 : -1;
					for (int road = 0; road < 4; road++)
					{
						if (view.road[road] == 0)continue;//这条路本身被封死了

						//这里的判断是这条路还有无防守逻辑
						if (change[my][en].tankdeath[side][(road >= 2) ? 1 - side : side])
							continue;

						if (change[my][en].roaddefence[side][road] == -100)continue;//表示这条路径已经不具有参考价值了
						if (change[my][en].roaddefence[side][road] == 0 && unchange.roaddefence[side][road] == 0)continue;
						if (change[my][en].roaddefence[side][road] * unchange.roaddefence[side][road] <= 0)
						{
							int key = (change[my][en].roaddefence[side][road] - unchange.roaddefence[side][road] >= 0) ? 1 : -1;
							double useful = 1;//表示这条gg的路径是否真的是最短的路径 如果不是 没必要考虑这种问题
							int find = (road < 2) ? (side == 1) : (side == 0);//这里找到的是我方对应的tank的编号 相当于是tank[side][j]-tank[1-side][1-j]
							if ((unchange.roadimportance[side][find] == 0 && (road == 0 || road == 3)) || (unchange.roadimportance[side][find] == 1 && (road == 1 || road == 2)))
								useful = 4;
							int place = (road < 2) ? 0 : 1;
							if (change[my][en].whoiscloser[place] == -1)useful = 4;
							if (change[my][en].whoiscloser[place] == side)useful = 4;
							choosemartix[my][en].second += qq * (key)* paralist.roadcontrol / useful * sigmoid(unchange.roaddefence[side][road]);
						
						}
						else
							choosemartix[my][en].second += qq * (change[my][en].roaddefence[side][road] - unchange.roaddefence[side][road]) * sigmoid(unchange.roaddefence[side][road]);
					}
					//最短路径估值
					for (int i = 0; i < 2; i++)
					{
						if (change[my][en].tankdeath[side][i])continue;
						int roadchoose[2];
						if (i == side)roadchoose[0] = 0, roadchoose[1] = 1;
						else roadchoose[0] = 2, roadchoose[1] = 3;
						double moveadder = 1;
						if (my == 11 && en == 4)
							my = my;
						for (int j = 0; j < 2; j++)
						{
							if (view.road[roadchoose[j]] == 0)continue;
							
							if (change[my][en].roaddefence[1 - side][roadchoose[j]] <= 0)//表示不具有守住的能力
								moveadder = paralist.movedelta;	
						}
						//再判断对方是不是到的比我们快
						
						int place = (side == i) ? 0 : 1;
						if (change[my][en].whoiscloser[place] != side && change[my][en].whoiscloser[place] != -1)
							moveadder = 1;
						choosemartix[my][en].second += qq * (-change[my][en].delta_minarrive[side][i]) * moveadder;
					}
				}
				tempstore temps; temps.number = en; temps.value = choosemartix[my][en].second;
				lowvalue.push(temps);
				if ((int)lowvalue.size() > paralist.open_dimension)lowvalue.pop();
				totalvalue += choosemartix[my][en].second;
				change[my][en].value = choosemartix[my][en].second;
				maxvalue = std::max(choosemartix[my][en].second, maxvalue);
				minvalue = std::min(choosemartix[my][en].second, minvalue);
			}
			outtempstore out;
			while (!lowvalue.empty())
			{
				tempstore temps = lowvalue.top();
				lowvalue.pop();
				out.ac.push_back(temps.number);
				out.eachvalue.push_back(temps.value);
				out.value += temps.value;
			}
			out.meaninside = out.value / out.ac.size();
			out.myaction = my;
			chooser.push(out);
			if ((int)chooser.size() > paralist.open_dimension)chooser.pop();

		}

		totalvalue /= (unchange.nummy * unchange.numen);
		double limitation = (totalvalue >= 0) ? totalvalue * paralist.limitation : totalvalue / paralist.limitation;

		timelog[clock_num++] = clock();
		if (debugging)
		{
			cout << "选择的限制大小为" << limitation << "，最大值为" << maxvalue << "，最小为" << minvalue << endl;
			for (int my = 0; my < unchange.nummy; my++)
			{
				for (int en = 0; en < unchange.numen; en++)
				{
					//cout << std::setw(6) << setiosflags(ios::fixed) << setprecision(2) << choosemartix[my][en].second;
				}
				cout << endl << endl;
			}
		}
		//hhhhhhh终点
		return chooser;
	}
	
};

returnstruct centralcalculation(TankField *ptr, int layer = 1)
{
	if (layer == 2)
		debugging = 0;
	returnstruct myself;
	int myside = ptr->mySide;
	vector<pair<Action,Action>> aclist[2];
	clock_t oncestart = clock();

	//可行操作列举
	for (int side = 0; side < 2; side++)
	{
		vector<Action> tempac; tempac.clear();
		//对1号tank来说
		if (!ptr->tankAlive[side][1])tempac.push_back(Stay);
		else
			for (int move = -1; move < 8; move++)
				if (ptr->ActionIsValid(side, 1, Action(move)))
					tempac.push_back(Action(move));
		//action对形成	
		for (int move = -2; move < 8; move++)
		{
			if (move == 3 && side == 1)
				side = side;
			if (ptr->tankAlive[side][0] && move != -2)
				if (ptr->ActionIsValid(side, 0, Action(move)))
				{
					Action *acpair = new Action[2];
					acpair[0] = Action(move);
					for (int j = 0; j < (int)tempac.size(); j++)
					{
						acpair[1] = tempac[j];
						aclist[side].push_back(pair<Action,Action>(acpair[0],acpair[1]));
					}
					
				}
			if (!ptr->tankAlive[side][0])
			{
				Action *acpair = new Action[2];
				acpair[0] = Stay;
				for (int j = 0; j < (int)tempac.size(); j++)
				{
					acpair[1] = tempac[j];
					aclist[side].push_back(pair<Action,Action>(acpair[0],acpair[1]));
				}
				break;
			}
		}
	}

	int sizen = aclist[myside].size();
	int sizem = aclist[1 - myside].size();
	/*
	
	std::pair<int[2],double> **value = new std::pair<int[2],double>*[paralist.open_dimension];
	for (int i = 0; i < paralist.open_dimension; i++)
		value[i] = new std::pair<int[2],double>[paralist.open_dimension];
	accessfield A;
	value = A.DoEvaluate(*ptr, aclist);
	*/

	priority_queue<outtempstore> next;
	accessfield A; next = A.DoEvaluate(*ptr, aclist,layer);

	clock_t ender = clock() - oncestart;
	paralist.runtime = ender - (timelog[viewtime] - timelog[viewtime - 1]);

	if (layer == 1)
	{
		int templayer = 1;
		while (true)
		{
			if (((double)pow(paralist.open_dimension, 2 * templayer) - 1) / (paralist.open_dimension * paralist.open_dimension - 1) * paralist.alpha > paralist.givetime/paralist.runtime)
			{
				if(debugging)
					cout << ((double)pow(paralist.open_dimension, 2 * templayer) - 1) / (paralist.open_dimension * paralist.open_dimension - 1) * paralist.alpha * paralist.runtime << "为理论所需用时" << endl;
				templayer--;
				break;
			}
			templayer++;
		}
		paralist.open_layer = max(templayer,2);
	}
	int sizenumber = next.size();
	returnstruct tempsave;
	if (debugging)
	{
		cout << "第" << layer << "层，地图为:" << endl;
		ptr->DebugPrint();
		cout << myside << "方较为优秀的操作：" << endl;
	}
	for (int roader = 0; roader < sizenumber; roader++)
	{
		outtempstore alpharoad = next.top(); next.pop();
		if (debugging)
				cout << aclist[myside][alpharoad.myaction].first << aclist[myside][alpharoad.myaction].second << "   ";
		clock_t temptime = clock();
		if (temptime - timelog[0] > paralist.givetime - paralist.open_dimension * paralist.runtime)
			paralist.emergency = true;
		int hissize = alpharoad.ac.size();
		//for (int en = 0; en < hissize; en++)
		//	alpharoad.value = min(alpharoad.value, alpharoad.eachvalue[en]);
		alpharoad.value = 1000;
		for (int i = 0; i < hissize; i++)
			alpharoad.value = min(alpharoad.value, alpharoad.eachvalue[i]);
		//if (!(paralist.emergency || layer == paralist.open_layer))//打开下一层
		if(layer != paralist.open_layer)
		{
			alpharoad.value = 1000;
			for (int en = 0; en < hissize; en++)
			{
				double betavalue = alpharoad.eachvalue[en];
				TankField temp = *ptr;

				temp.nextAction[myside][0] = aclist[myside][alpharoad.myaction].first;
				temp.nextAction[myside][1] = aclist[myside][alpharoad.myaction].second;
				temp.nextAction[1 - myside][0] = aclist[1 - myside][alpharoad.ac[en]].first;
				temp.nextAction[1 - myside][1] = aclist[1 - myside][alpharoad.ac[en]].second;
				if (layer == 1 && en == 0 && next.size() == 1)
					layer = layer;

				temp.DoAction();
				tempsave = centralcalculation(&temp, layer + 1);
				
				betavalue += paralist.lessen * tempsave.value;
				alpharoad.value = min(alpharoad.value, betavalue);

				if (alpharoad.value < myself.value)
					break;
			}
		}
		if (myself.value <= alpharoad.value)
		{
			myself.value = alpharoad.value;
			myself.bestac[0] = aclist[myside][alpharoad.myaction].first; myself.bestac[1] = aclist[myside][alpharoad.myaction].second;
		}
	}
	if (debugging)
		cout << endl;
	return myself;
}



int main()
{
	srand((unsigned)time(nullptr));
	string data, globaldata;
	TankGame::ReadInput(cin, data, globaldata);//读入之前的操作
	if (debugging)
	{
		field->DebugPrint();//打印场地
		cout << "我方阵营是" << field->mySide << endl;
	}
	timelog[clock_num++] = clock();
	returnstruct result = centralcalculation(field);
	timelog[clock_num++] = clock();
	if(debugging)
		for (int i = 1; i < clock_num; i++)
		{
			cout << "时段" << i << "用时为" << timelog[i] - timelog[i - 1] << endl;
		}
	//cout << "选择打开层数为" << paralist.open_layer << ",runtime为" << paralist.runtime << endl;
	//cout << "总用时" << timelog[clock_num - 1] - timelog[0] << "毫秒" << endl;
	//TankGame::SubmitAndExit(RandAction(0), RandAction(1));//随机输出两个步数
	TankGame::SubmitAndExit(result.bestac[0],result.bestac[1]);
}