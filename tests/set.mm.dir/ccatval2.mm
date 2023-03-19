include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cmin.mm"
include "cif.mm"
include "cconcat.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "ccatfval.mm"
include "3adant3.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "fzodisj.mm"
include "minel.mm"
include "mpan2.mm"
include "3ad2ant3.mm"
include "iffalsed.mm"
include "sylan9eqr.mm"
include "wa.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "wrdfin.mm"
include "adantr.mm"
include "hashcl.mm"
include "cuz.mm"
include "fzoss1.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "3syl.mm"
include "sseld.mm"
include "3impia.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem ccatval2
  let cB: class B
  let cS: class S
  let cT: class T
  let cI: class I
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B /\ I e. ( ( # ` S ) ..^ ( ( # ` S ) + ( # ` T ) ) ) ) -> ( ( S ++ T ) ` I ) = ( T ` ( I - ( # ` S ) ) ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cI
    cS
    chash
    cfv
    #
    @3
    cT
    chash
    cfv
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    vx
    cI
    vx
    cv
    #
    cc0
    @3
    cfzo
    co
    #
    wcel
    #
    @8
    cS
    cfv
    #
    @8
    @3
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    cI
    @3
    cmin
    co
    #
    cT
    cfv
    #
    cc0
    @4
    cfzo
    co
    #
    cS
    cT
    cconcat
    co
    #
    cvv
    @1
    @2
    @18
    vx
    @17
    @14
    cmpt
    wceq
    @6
    vx
    cS
    cT
    @0
    @0
    ccatfval
    3adant3
    @8
    cI
    wceq
    #
    @7
    @14
    cI
    @9
    wcel
    #
    cI
    cS
    cfv
    #
    @16
    cif
    @16
    @19
    @10
    @20
    @11
    @13
    @21
    @16
    @8
    cI
    @9
    eleq1
    @8
    cI
    cS
    fveq2
    @19
    @12
    @15
    cT
    @8
    cI
    @3
    cmin
    oveq1
    fveq2d
    ifbieq12d
    @7
    @20
    @21
    @16
    @6
    @1
    @20
    wn
    #
    @2
    @6
    @9
    @5
    cin
    c0
    wceq
    @22
    cc0
    @3
    @4
    fzodisj
    cI
    @5
    @9
    minel
    mpan2
    3ad2ant3
    iffalsed
    sylan9eqr
    @1
    @2
    @6
    cI
    @17
    wcel
    @1
    @2
    wa
    #
    @5
    @17
    cI
    @23
    cS
    cfn
    wcel
    #
    @3
    cn0
    wcel
    @5
    @17
    wss
    #
    @1
    @24
    @2
    cB
    cS
    wrdfin
    adantr
    cS
    hashcl
    @25
    @3
    cc0
    cuz
    cfv
    cn0
    @3
    cc0
    @4
    fzoss1
    nn0uz
    eleq2s
    3syl
    sseld
    3impia
    @7
    @15
    cT
    fvexd
    fvmptd
end
