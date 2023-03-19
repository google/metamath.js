include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cr.mm"
include "ioran.mm"
include "anbi2i.mm"
include "anbi12i.mm"
include "bitri.mm"
include "w3o.mm"
include "simplll.mm"
include "elxr.mm"
include "sylib.mm"
include "idd.mm"
include "wi.mm"
include "simprlr.mm"
include "adantl.mm"
include "pm2.21d.mm"
include "expdimp.mm"
include "simplrr.mm"
include "imp.mm"
include "simpllr.mm"
include "0xr.mm"
include "wor.mm"
include "xrltso.mm"
include "solin.mm"
include "mpan.mm"
include "sylancl.mm"
include "mpjao3dan.mm"
include "simprll.mm"
include "3jaod.mm"
include "mpd.mm"
include "syl2anb.mm"
include "anassrs.mm"

theorem xmullem
  let cA: class A
  let cB: class B


  assert |- ( ( ( ( ( A e. RR* /\ B e. RR* ) /\ -. ( A = 0 \/ B = 0 ) ) /\ -. ( ( ( 0 < B /\ A = +oo ) \/ ( B < 0 /\ A = -oo ) ) \/ ( ( 0 < A /\ B = +oo ) \/ ( A < 0 /\ B = -oo ) ) ) ) /\ -. ( ( ( 0 < B /\ A = -oo ) \/ ( B < 0 /\ A = +oo ) ) \/ ( ( 0 < A /\ B = -oo ) \/ ( A < 0 /\ B = +oo ) ) ) ) -> A e. RR )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wo
    wn
    #
    wa
    #
    cc0
    cB
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    wa
    #
    cB
    cc0
    clt
    wbr
    #
    cA
    cmnf
    wceq
    #
    wa
    #
    wo
    #
    cc0
    cA
    clt
    wbr
    #
    cB
    cpnf
    wceq
    #
    wa
    #
    cA
    cc0
    clt
    wbr
    #
    cB
    cmnf
    wceq
    #
    wa
    #
    wo
    #
    wo
    wn
    #
    @7
    @11
    wa
    #
    @10
    @8
    wa
    #
    wo
    #
    @14
    @18
    wa
    #
    @17
    @15
    wa
    #
    wo
    #
    wo
    wn
    #
    cA
    cr
    wcel
    #
    @6
    @2
    @3
    wn
    #
    @4
    wn
    #
    wa
    #
    wa
    #
    @9
    wn
    #
    @12
    wn
    #
    wa
    #
    @16
    wn
    @19
    wn
    wa
    #
    wa
    #
    @22
    wn
    #
    @23
    wn
    #
    wa
    #
    @25
    wn
    @26
    wn
    wa
    #
    wa
    #
    wa
    #
    @29
    @21
    @28
    wa
    @5
    @32
    @2
    @3
    @4
    ioran
    anbi2i
    @21
    @38
    @28
    @43
    @21
    @13
    wn
    #
    @20
    wn
    #
    wa
    @38
    @13
    @20
    ioran
    @45
    @36
    @46
    @37
    @9
    @12
    ioran
    @16
    @19
    ioran
    anbi12i
    bitri
    @28
    @24
    wn
    #
    @27
    wn
    #
    wa
    @43
    @24
    @27
    ioran
    @47
    @41
    @48
    @42
    @22
    @23
    ioran
    @25
    @26
    ioran
    anbi12i
    bitri
    anbi12i
    @33
    @44
    wa
    #
    @29
    @8
    @11
    w3o
    #
    @29
    @49
    @0
    @50
    @0
    @1
    @32
    @44
    simplll
    cA
    elxr
    sylib
    @49
    @29
    @29
    @8
    @11
    @49
    @29
    idd
    @49
    @10
    @8
    @29
    wi
    #
    @4
    @7
    @49
    @10
    @8
    @29
    @49
    @23
    @29
    @44
    @40
    @33
    @38
    @39
    @40
    @42
    simprlr
    adantl
    pm2.21d
    expdimp
    @49
    @4
    @51
    @49
    @4
    @51
    @2
    @30
    @31
    @44
    simplrr
    #
    pm2.21d
    imp
    @49
    @7
    @8
    @29
    @49
    @9
    @29
    @44
    @34
    @33
    @34
    @35
    @37
    @43
    simplll
    adantl
    pm2.21d
    expdimp
    @49
    @1
    cc0
    cxr
    wcel
    #
    @10
    @4
    @7
    w3o
    #
    @0
    @1
    @32
    @44
    simpllr
    0xr
    cxr
    clt
    wor
    @1
    @53
    wa
    @54
    xrltso
    cxr
    cB
    cc0
    clt
    solin
    mpan
    sylancl
    #
    mpjao3dan
    @49
    @10
    @11
    @29
    wi
    #
    @4
    @7
    @49
    @10
    @11
    @29
    @49
    @12
    @29
    @44
    @35
    @33
    @34
    @35
    @37
    @43
    simpllr
    adantl
    pm2.21d
    expdimp
    @49
    @4
    @56
    @49
    @4
    @56
    @52
    pm2.21d
    imp
    @49
    @7
    @11
    @29
    @49
    @22
    @29
    @44
    @39
    @33
    @38
    @39
    @40
    @42
    simprll
    adantl
    pm2.21d
    expdimp
    @55
    mpjao3dan
    3jaod
    mpd
    syl2anb
    anassrs
end
