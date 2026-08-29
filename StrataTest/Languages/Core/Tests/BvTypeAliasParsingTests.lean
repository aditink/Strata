import Strata

def compactBvTypeAliases := #strata
program Core;

datatype CompactBvTypeAliases {
  One(one : bv1),
  Eight(eight : bv8),
  Sixteen(sixteen : bv16),
  ThirtyTwo(thirtyTwo : bv32),
  SixtyFour(sixtyFour : bv64),
  OneTwentyEight(oneTwentyEight : bv128)
};
#end

#check compactBvTypeAliases
