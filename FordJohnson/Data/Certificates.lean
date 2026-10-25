import FordJohnson.Lib.Certificate
import FordJohnson.Data.T21
import FordJohnson.Data.T42

namespace FordJohnson

open Certificate

set_option maxRecDepth 100000

theorem insert_five_into_twenty_one : InsertionBound 21 5 24 :=
  verify_sound (show verify Data.t21_5 21 5 24 = true by native_decide)

theorem insert_four_into_forty_two : InsertionBound 42 4 23 :=
  verify_sound (show verify Data.t42_4 42 4 23 = true by native_decide)

end FordJohnson
