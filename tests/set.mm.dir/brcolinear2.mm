include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cbtwn.mm"
include "w3o.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "colinrel.mm"
include "brrelexi.mm"
include "a1i.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "rexlimivw.mm"
include "wb.mm"
include "coprab.mm"
include "ccnv.mm"
include "df-br.mm"
include "df-colinear.mm"
include "eleq2i.mm"
include "bitri.mm"
include "opex.mm"
include "opelcnvg.mm"
include "mpan2.mm"
include "3ad2ant3.mm"
include "syl5bb.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "opeq1.mm"
include "breq2d.mm"
include "breq1.mm"
include "opeq2.mm"
include "3orbi123d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "3anbi3d.mm"
include "3anbi1d.mm"
include "eloprabg.mm"
include "bitrd.mm"
include "3expia.mm"
include "pm5.21ndd.mm"

theorem brcolinear2
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vn: setvar n
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r

  disjoint P n
  disjoint Q n
  disjoint R n
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint P p
  disjoint p q
  disjoint P q
  disjoint p r
  disjoint P r
  disjoint Q p
  disjoint Q q
  disjoint q r
  disjoint Q r
  disjoint R p
  disjoint R q
  disjoint R r
  assert |- ( ( Q e. V /\ R e. W ) -> ( P Colinear <. Q , R >. <-> E. n e. NN ( ( P e. ( EE ` n ) /\ Q e. ( EE ` n ) /\ R e. ( EE ` n ) ) /\ ( P Btwn <. Q , R >. \/ Q Btwn <. R , P >. \/ R Btwn <. P , Q >. ) ) ) )

  proof
    cQ
    cV
    wcel
    #
    cR
    cW
    wcel
    #
    wa
    #
    cP
    cvv
    wcel
    #
    cP
    cQ
    cR
    cop
    #
    ccolin
    wbr
    #
    cP
    vn
    cv
    cee
    cfv
    #
    wcel
    #
    cQ
    @6
    wcel
    #
    cR
    @6
    wcel
    #
    w3a
    #
    cP
    @4
    cbtwn
    wbr
    #
    cQ
    cR
    cP
    cop
    #
    cbtwn
    wbr
    #
    cR
    cP
    cQ
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    #
    @5
    @3
    wi
    @2
    cP
    @4
    ccolin
    colinrel
    brrelexi
    a1i
    @18
    @3
    wi
    @2
    @17
    @3
    vn
    cn
    @10
    @3
    @16
    @7
    @8
    @3
    @9
    cP
    @6
    elex
    3ad2ant1
    adantr
    rexlimivw
    a1i
    @0
    @1
    @3
    @5
    @18
    wb
    @0
    @1
    @3
    w3a
    #
    @5
    @4
    cP
    cop
    vp
    cv
    #
    @6
    wcel
    #
    vq
    cv
    #
    @6
    wcel
    #
    vr
    cv
    #
    @6
    wcel
    #
    w3a
    #
    @20
    @22
    @24
    cop
    #
    cbtwn
    wbr
    #
    @22
    @24
    @20
    cop
    #
    cbtwn
    wbr
    #
    @24
    @20
    @22
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    #
    vq
    vr
    vp
    coprab
    #
    wcel
    #
    @18
    @5
    cP
    @4
    cop
    #
    @36
    ccnv
    #
    wcel
    #
    @19
    @37
    @5
    @38
    ccolin
    wcel
    @40
    cP
    @4
    ccolin
    df-br
    ccolin
    @39
    @38
    vn
    vp
    vq
    vr
    df-colinear
    eleq2i
    bitri
    @3
    @0
    @40
    @37
    wb
    #
    @1
    @3
    @4
    cvv
    wcel
    @41
    cQ
    cR
    opex
    cP
    @4
    cvv
    cvv
    @36
    opelcnvg
    mpan2
    3ad2ant3
    syl5bb
    @35
    @21
    @8
    @25
    w3a
    #
    @20
    cQ
    @24
    cop
    #
    cbtwn
    wbr
    #
    cQ
    @29
    cbtwn
    wbr
    #
    @24
    @20
    cQ
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    @21
    @8
    @9
    w3a
    #
    @20
    @4
    cbtwn
    wbr
    #
    cQ
    cR
    @20
    cop
    #
    cbtwn
    wbr
    #
    cR
    @46
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    @18
    vq
    vr
    vp
    cQ
    cR
    cP
    cV
    cW
    cvv
    @22
    cQ
    wceq
    #
    @34
    @49
    vn
    cn
    @57
    @26
    @42
    @33
    @48
    @57
    @23
    @8
    @21
    @25
    @22
    cQ
    @6
    eleq1
    3anbi2d
    @57
    @28
    @44
    @30
    @45
    @32
    @47
    @57
    @27
    @43
    @20
    cbtwn
    @22
    cQ
    @24
    opeq1
    breq2d
    @22
    cQ
    @29
    cbtwn
    breq1
    @57
    @31
    @46
    @24
    cbtwn
    @22
    cQ
    @20
    opeq2
    breq2d
    3orbi123d
    anbi12d
    rexbidv
    @24
    cR
    wceq
    #
    @49
    @56
    vn
    cn
    @58
    @42
    @50
    @48
    @55
    @58
    @25
    @9
    @21
    @8
    @24
    cR
    @6
    eleq1
    3anbi3d
    @58
    @44
    @51
    @45
    @53
    @47
    @54
    @58
    @43
    @4
    @20
    cbtwn
    @24
    cR
    cQ
    opeq2
    breq2d
    @58
    @29
    @52
    cQ
    cbtwn
    @24
    cR
    @20
    opeq1
    breq2d
    @24
    cR
    @46
    cbtwn
    breq1
    3orbi123d
    anbi12d
    rexbidv
    @20
    cP
    wceq
    #
    @56
    @17
    vn
    cn
    @59
    @50
    @10
    @55
    @16
    @59
    @21
    @7
    @8
    @9
    @20
    cP
    @6
    eleq1
    3anbi1d
    @59
    @51
    @11
    @53
    @13
    @54
    @15
    @20
    cP
    @4
    cbtwn
    breq1
    @59
    @52
    @12
    cQ
    cbtwn
    @20
    cP
    cR
    opeq2
    breq2d
    @59
    @46
    @14
    cR
    cbtwn
    @20
    cP
    cQ
    opeq1
    breq2d
    3orbi123d
    anbi12d
    rexbidv
    eloprabg
    bitrd
    3expia
    pm5.21ndd
end
