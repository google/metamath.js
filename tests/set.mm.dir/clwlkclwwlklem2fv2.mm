include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "ccnv.mm"
include "cc0.mm"
include "cif.mm"
include "cfzo.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wn.mm"
include "wi.mm"
include "cz.mm"
include "simpr.mm"
include "nn0z.mm"
include "2z.mm"
include "jctir.mm"
include "zsubcl.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "nn0re.mm"
include "2re.mm"
include "resubcld.mm"
include "lttri3.mm"
include "syl2anr.mm"
include "simpl.mm"
include "syl6bi.mm"
include "syld.mm"
include "com13.mm"
include "pm2.43i.mm"
include "impcom.mm"
include "iffalsed.mm"
include "fveq2.mm"
include "adantl.mm"
include "preq1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "cn.mm"
include "subge0d.mm"
include "biimpar.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "nn0ge2m1nn.mm"
include "1red.mm"
include "1lt2.mm"
include "ltsub2dd.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem clwlkclwwlklem2fv2
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cV: class V
  let cI: class I
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint I x
  assert |- ( ( ( # ` P ) e. NN0 /\ 2 <_ ( # ` P ) ) -> ( F ` ( ( # ` P ) - 2 ) ) = ( `' E ` { ( P ` ( ( # ` P ) - 2 ) ) , ( P ` 0 ) } ) )

  proof
    cP
    chash
    cfv
    #
    cn0
    wcel
    #
    c2
    @0
    cle
    wbr
    #
    wa
    #
    vx
    @0
    c2
    cmin
    co
    #
    vx
    cv
    #
    @4
    clt
    wbr
    #
    @5
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    cP
    cfv
    cpr
    cE
    ccnv
    #
    cfv
    #
    @7
    cc0
    cP
    cfv
    #
    cpr
    #
    @8
    cfv
    #
    cif
    #
    @4
    cP
    cfv
    #
    @10
    cpr
    #
    @8
    cfv
    #
    cc0
    @0
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cF
    cvv
    cF
    vx
    @18
    @13
    cmpt
    wceq
    @3
    clwlkclwwlklem2.f
    a1i
    @3
    @5
    @4
    wceq
    #
    wa
    #
    @13
    @12
    @16
    @20
    @6
    @9
    @12
    @19
    @3
    @6
    wn
    #
    @19
    @3
    @21
    wi
    @3
    @19
    @19
    @21
    @3
    @19
    @5
    cz
    wcel
    #
    @19
    @21
    wi
    #
    @3
    @19
    @22
    @20
    @5
    @4
    cz
    @3
    @19
    simpr
    @3
    @4
    cz
    wcel
    #
    @19
    @1
    @24
    @2
    @1
    @0
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    wa
    #
    @24
    @1
    @25
    @26
    @0
    nn0z
    2z
    jctir
    #
    @0
    c2
    zsubcl
    #
    syl
    adantr
    adantr
    eqeltrd
    ex
    @3
    @22
    @23
    @3
    @22
    wa
    @19
    @21
    @4
    @5
    clt
    wbr
    wn
    #
    wa
    #
    @21
    @22
    @5
    cr
    wcel
    @4
    cr
    wcel
    #
    @19
    @31
    wb
    @3
    @5
    zre
    @1
    @32
    @2
    @1
    @0
    c2
    @0
    nn0re
    #
    c2
    cr
    wcel
    #
    @1
    2re
    a1i
    #
    resubcld
    adantr
    @5
    @4
    lttri3
    syl2anr
    @21
    @30
    simpl
    syl6bi
    ex
    syld
    com13
    pm2.43i
    impcom
    iffalsed
    @20
    @11
    @15
    @8
    @20
    @7
    @14
    @10
    @19
    @7
    @14
    wceq
    @3
    @5
    @4
    cP
    fveq2
    adantl
    preq1d
    fveq2d
    eqtrd
    @3
    @4
    cn0
    wcel
    #
    @17
    cn
    wcel
    @4
    @17
    clt
    wbr
    @4
    @18
    wcel
    @3
    @24
    cc0
    @4
    cle
    wbr
    #
    @36
    @3
    @27
    @24
    @1
    @27
    @2
    @28
    adantr
    @29
    syl
    @1
    @37
    @2
    @1
    @0
    c2
    @33
    @35
    subge0d
    biimpar
    @4
    elnn0z
    sylanbrc
    @0
    nn0ge2m1nn
    @3
    c1
    c2
    @0
    @3
    1red
    @34
    @3
    2re
    a1i
    @1
    @0
    cr
    wcel
    @2
    @33
    adantr
    c1
    c2
    clt
    wbr
    @3
    1lt2
    a1i
    ltsub2dd
    @4
    @17
    elfzo0
    syl3anbrc
    @3
    @15
    @8
    fvexd
    fvmptd
end
