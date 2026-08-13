module

public meta import HJOA3.FlagStraightening

/-!
# Encoding tests for `HJOA3.FlagStraightening`
-/

set_option linter.hashCommand false

namespace HJOA3

#guard xChain 0 [3] * yChain 1 2 = 32
#guard mChain 0 [5] = 32

#guard xChain 0 [1, 2] * yChain 2 1 = 18
#guard mChain 0 [2, 1] = 18

#guard xChain 0 [1, 3] * yChain 2 2 = 108
#guard mChain 0 [3, 2] = 108

#guard xChain 0 [1, 2, 2] * yChain 3 0 = 12
#guard mChain 0 [1, 1, 0] = 12

#guard xChain 0 [2, 2, 3] * yChain 3 1 = 128
#guard mChain 0 [3, 0, 1] = 128

#guard xChain 0 [1, 3, 3] * yChain 3 2 = 576
#guard mChain 0 [3, 2, 0] = 576

#guard gaps [1, 3, 3] = [2, 0]
#guard gaps [2, 2, 3] = [0, 1]

end HJOA3
