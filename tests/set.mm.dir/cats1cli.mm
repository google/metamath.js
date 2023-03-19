include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "s1cli.mm"
include "ccatcl.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem cats1cli
  let cS: class S
  let cT: class T
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cli.2: |- S e. Word _V


  assert |- T e. Word _V

  proof
    cT
    cS
    cX
    cs1
    #
    cconcat
    co
    #
    cvv
    cword
    #
    cats1cld.1
    cS
    @2
    wcel
    @0
    @2
    wcel
    @1
    @2
    wcel
    cats1cli.2
    cX
    s1cli
    cvv
    cS
    @0
    ccatcl
    mp2an
    eqeltri
end
