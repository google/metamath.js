include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cn.mm"
include "wa.mm"
include "simplll.mm"
include "nnre.mm"
include "ad3antlr.mm"
include "prmz.mm"
include "zred.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "lttrd.mm"
include "wral.mm"
include "arch.mm"
include "prmunb.mm"
include "rgen.mm"
include "r19.29r.mm"
include "sylancl.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "sylibr.mm"
include "reximddv2.mm"
include "c1.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "1nn.mm"
include "ne0i.mm"
include "r19.9rzv.mm"
include "mp2b.mm"

theorem prmunb2
  let cA: class A
  let vp: setvar p
  let vn: setvar n

  disjoint A p
  disjoint n p
  disjoint A n
  assert |- ( A e. RR -> E. p e. Prime A < p )

  proof
    cA
    cr
    wcel
    #
    cA
    vp
    cv
    #
    clt
    wbr
    #
    vp
    cprime
    wrex
    #
    vn
    cn
    wrex
    #
    @3
    @0
    cA
    vn
    cv
    #
    clt
    wbr
    #
    @5
    @1
    clt
    wbr
    #
    wa
    #
    @2
    vn
    vp
    cn
    cprime
    @0
    @5
    cn
    wcel
    #
    wa
    #
    @1
    cprime
    wcel
    #
    wa
    #
    @8
    wa
    cA
    @5
    @1
    @0
    @9
    @11
    @8
    simplll
    @9
    @5
    cr
    wcel
    @0
    @11
    @8
    @5
    nnre
    ad3antlr
    @11
    @1
    cr
    wcel
    @10
    @8
    @11
    @1
    @1
    prmz
    zred
    ad2antlr
    @12
    @6
    @7
    simprl
    @12
    @6
    @7
    simprr
    lttrd
    @0
    @6
    @7
    vp
    cprime
    wrex
    #
    wa
    #
    vn
    cn
    wrex
    #
    @8
    vp
    cprime
    wrex
    #
    vn
    cn
    wrex
    @0
    @6
    vn
    cn
    wrex
    @13
    vn
    cn
    wral
    @15
    cA
    vn
    arch
    @13
    vn
    cn
    @5
    vp
    prmunb
    rgen
    @6
    @13
    vn
    cn
    r19.29r
    sylancl
    @16
    @14
    vn
    cn
    @6
    @7
    vp
    cprime
    r19.42v
    rexbii
    sylibr
    reximddv2
    c1
    cn
    wcel
    cn
    c0
    wne
    @3
    @4
    wb
    1nn
    cn
    c1
    ne0i
    @3
    vn
    cn
    r19.9rzv
    mp2b
    sylibr
end
