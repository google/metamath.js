include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "wa.mm"
include "cr.mm"
include "cle.mm"
include "nn0nndivcl.mm"
include "reflcl.mm"
include "syl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "3jca.mm"
include "adantr.mm"
include "fldivnn0le.mm"
include "simpr.mm"
include "cc0.mm"
include "wb.mm"
include "nn0re.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "3anim123i.mm"
include "ltdiv1.mm"
include "mpbid.mm"
include "lelttr.mm"
include "sylc.mm"
include "ex.mm"

theorem flltdivnn0lt
  let cK: class K
  let cL: class L
  let cN: class N


  assert |- ( ( K e. NN0 /\ N e. NN0 /\ L e. NN ) -> ( K < N -> ( |_ ` ( K / L ) ) < ( N / L ) ) )

  proof
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cL
    cn
    wcel
    #
    w3a
    #
    cK
    cN
    clt
    wbr
    #
    cK
    cL
    cdiv
    co
    #
    cfl
    cfv
    #
    cN
    cL
    cdiv
    co
    #
    clt
    wbr
    #
    @3
    @4
    wa
    #
    @6
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    w3a
    #
    @6
    @5
    cle
    wbr
    #
    @5
    @7
    clt
    wbr
    #
    wa
    @8
    @3
    @13
    @4
    @3
    @10
    @11
    @12
    @0
    @2
    @10
    @1
    @0
    @2
    wa
    @11
    @10
    cK
    cL
    nn0nndivcl
    #
    @5
    reflcl
    syl
    3adant2
    @0
    @2
    @11
    @1
    @16
    3adant2
    @1
    @2
    @12
    @0
    cN
    cL
    nn0nndivcl
    3adant1
    3jca
    adantr
    @9
    @14
    @15
    @3
    @14
    @4
    @0
    @2
    @14
    @1
    cK
    cL
    fldivnn0le
    3adant2
    adantr
    @9
    @4
    @15
    @3
    @4
    simpr
    @9
    cK
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    cc0
    cL
    clt
    wbr
    #
    wa
    #
    w3a
    #
    @4
    @15
    wb
    @3
    @22
    @4
    @0
    @17
    @1
    @18
    @2
    @21
    cK
    nn0re
    cN
    nn0re
    @2
    @19
    @20
    cL
    nnre
    cL
    nngt0
    jca
    3anim123i
    adantr
    cK
    cN
    cL
    ltdiv1
    syl
    mpbid
    jca
    @6
    @5
    @7
    lelttr
    sylc
    ex
end
