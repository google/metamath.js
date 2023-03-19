include "tb.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "biao.mm"
include "bicom.mm"
include "ax-r2.mm"
include "bile.mm"
include "wi2.mm"
include "wi1.mm"
include "orbile.mm"
include "imp3.mm"
include "lbtr.mm"
include "le2an.mm"
include "2bi.mm"
include "ax-r4.mm"
include "ran.mm"
include "ancom.mm"
include "lan.mm"
include "2or.mm"
include "2an.mm"
include "ax-r1.mm"
include "lea.mm"
include "3tr1.mm"
include "rbi.mm"
include "ler2an.mm"
include "anass.mm"
include "coman1.mm"
include "comcom7.mm"
include "bctr.mm"
include "an32.mm"
include "coman2.mm"
include "com2an.mm"
include "com2or.mm"
include "fh2c.mm"
include "wf.mm"
include "anor3.mm"
include "comanr1.mm"
include "comcom3.mm"
include "fh2rc.mm"
include "leao1.mm"
include "df2le2.mm"
include "dff.mm"
include "oran.mm"
include "an0r.mm"
include "3tr2.mm"
include "or0.mm"
include "3tr.mm"
include "an4.mm"
include "anidm.mm"
include "or0r.mm"
include "dfb.mm"
include "lor.mm"
include "bi3.mm"
include "mlaoml.mm"
include "bltr.mm"
include "letr.mm"

theorem mlaconj4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  assume mlaconj4.1: |- ( ( d == e ) ^ ( ( e ' ^ c ' ) v ( d ^ c ) ) ) =< ( d == c )
  assume mlaconj4.2: |- d = ( a v b )
  assume mlaconj4.3: |- e = ( a ^ b )


  assert |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =< ( a == c )

  proof
    wva
    wvb
    tb
    #
    wva
    wvc
    tb
    #
    wvb
    wvc
    tb
    #
    wo
    #
    wa
    wva
    wvb
    wo
    #
    wva
    wvb
    wa
    #
    tb
    #
    @5
    wn
    #
    wvc
    wn
    #
    wa
    #
    wvc
    @4
    wa
    #
    wo
    #
    wa
    #
    @1
    @0
    @6
    @3
    @11
    @0
    @6
    @0
    @5
    @4
    tb
    #
    @6
    wva
    wvb
    biao
    #
    @5
    @4
    bicom
    ax-r2
    bile
    @3
    @5
    wvc
    wi2
    wvc
    @4
    wi1
    wa
    @11
    wva
    wvb
    wvc
    orbile
    @5
    wvc
    @4
    imp3
    lbtr
    le2an
    @12
    wvd
    wve
    tb
    #
    wve
    wn
    #
    @8
    wa
    #
    wvd
    wvc
    wa
    #
    wo
    #
    wa
    #
    @1
    @20
    @12
    @15
    @6
    @19
    @11
    wvd
    @4
    wve
    @5
    mlaconj4.2
    mlaconj4.3
    2bi
    #
    @17
    @9
    @18
    @10
    @16
    @7
    @8
    wve
    @5
    mlaconj4.3
    ax-r4
    ran
    @18
    wvc
    wvd
    wa
    @10
    wvd
    wvc
    ancom
    wvd
    @4
    wvc
    mlaconj4.2
    lan
    ax-r2
    2or
    2an
    ax-r1
    @20
    @0
    @4
    wvc
    tb
    #
    wa
    #
    @1
    @20
    @0
    @22
    @20
    @15
    @0
    @15
    @19
    lea
    @6
    @13
    @15
    @0
    @4
    @5
    bicom
    @21
    @14
    3tr1
    lbtr
    @20
    wvd
    wvc
    tb
    @22
    mlaconj4.1
    wvd
    @4
    wvc
    mlaconj4.2
    rbi
    lbtr
    ler2an
    @23
    @0
    @2
    wa
    #
    @1
    @5
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @4
    wvc
    wa
    #
    @27
    @8
    wa
    #
    wo
    #
    wa
    #
    @5
    wvc
    wa
    #
    @30
    wo
    #
    @23
    @24
    @32
    @28
    @29
    wa
    #
    @28
    @30
    wa
    #
    wo
    @34
    @30
    @28
    @29
    @30
    @5
    @27
    @30
    wva
    wvb
    @30
    @25
    @26
    @8
    wa
    #
    wa
    #
    wva
    @25
    @26
    @8
    anass
    @38
    wva
    @25
    @37
    coman1
    comcom7
    bctr
    #
    @30
    @25
    @8
    wa
    #
    @26
    wa
    #
    wvb
    @25
    @26
    @8
    an32
    @41
    wvb
    @40
    @26
    coman2
    comcom7
    bctr
    #
    com2an
    @27
    @8
    coman1
    com2or
    @30
    @4
    wvc
    @30
    wva
    wvb
    @39
    @42
    com2or
    @30
    wvc
    @27
    @8
    coman2
    comcom7
    com2an
    fh2c
    @35
    @33
    @36
    @30
    @35
    @5
    @29
    wa
    #
    @27
    @29
    wa
    #
    wo
    @33
    wf
    wo
    @33
    @27
    @29
    @5
    @27
    @4
    wn
    #
    @29
    wva
    wvb
    anor3
    #
    @4
    @29
    @4
    wvc
    comanr1
    comcom3
    bctr
    @27
    wva
    wvb
    @27
    wva
    @25
    @26
    coman1
    comcom7
    @27
    wvb
    @25
    @26
    coman2
    comcom7
    com2an
    #
    fh2rc
    @43
    @33
    @44
    wf
    @43
    @5
    @4
    wa
    #
    wvc
    wa
    #
    @33
    @49
    @43
    @5
    @4
    wvc
    anass
    ax-r1
    @48
    @5
    wvc
    @5
    @4
    wva
    wvb
    wvb
    leao1
    df2le2
    ran
    ax-r2
    @27
    @4
    wa
    #
    wvc
    wa
    #
    wf
    wvc
    wa
    #
    @44
    wf
    @52
    @51
    wf
    @50
    wvc
    wf
    @27
    @27
    wn
    #
    wa
    #
    @50
    @27
    dff
    @50
    @54
    @4
    @53
    @27
    wva
    wvb
    oran
    lan
    ax-r1
    ax-r2
    ran
    ax-r1
    @27
    @4
    wvc
    anass
    wvc
    an0r
    3tr2
    2or
    @33
    or0
    3tr
    @36
    @5
    @30
    wa
    #
    @27
    @30
    wa
    #
    wo
    wf
    @30
    wo
    @30
    @27
    @30
    @5
    @27
    @8
    comanr1
    @47
    fh2rc
    @55
    wf
    @56
    @30
    @55
    wva
    @27
    wa
    #
    wvb
    @8
    wa
    #
    wa
    #
    wf
    @58
    wa
    #
    wf
    wva
    wvb
    @27
    @8
    an4
    @60
    @59
    wf
    @57
    @58
    wf
    @26
    wa
    wva
    @25
    wa
    #
    @26
    wa
    wf
    @57
    wf
    @61
    @26
    wva
    dff
    ran
    @26
    an0r
    wva
    @25
    @26
    anass
    3tr2
    ran
    ax-r1
    @58
    an0r
    3tr
    @56
    @27
    @27
    wa
    #
    @8
    wa
    #
    @30
    @63
    @56
    @27
    @27
    @8
    anass
    ax-r1
    @62
    @27
    @8
    @27
    anidm
    ran
    ax-r2
    2or
    @30
    or0r
    3tr
    2or
    ax-r2
    @0
    @28
    @22
    @31
    wva
    wvb
    dfb
    @22
    @29
    @45
    @8
    wa
    #
    wo
    #
    @31
    @4
    wvc
    dfb
    @31
    @65
    @30
    @64
    @29
    @27
    @45
    @8
    @46
    ran
    lor
    ax-r1
    ax-r2
    2an
    wva
    wvb
    wvc
    bi3
    3tr1
    wva
    wvb
    wvc
    mlaoml
    bltr
    letr
    bltr
    letr
end
