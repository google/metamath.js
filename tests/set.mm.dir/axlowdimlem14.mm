include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "w3a.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "wa.mm"
include "wfn.mm"
include "cr.mm"
include "wf.mm"
include "cee.mm"
include "axlowdimlem10.mm"
include "elee.mm"
include "adantr.mm"
include "mpbid.mm"
include "ffn.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "3impdi.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "caddc.mm"
include "fznatpl1.mm"
include "3adant3.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "axlowdimlem11.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "addcan2.mm"
include "mp3an3.mm"
include "3adant1.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "axlowdimlem12.mm"
include "syl2anc.mm"
include "3netr4d.mm"
include "df-ne.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "syl5bbr.mm"
include "rspcev.mm"
include "ex.mm"
include "rexnal.mm"
include "3imtr3g.mm"
include "con4d.mm"
include "sylbid.mm"

theorem axlowdimlem14
  let cQ: class Q
  let cR: class R
  let cI: class I
  let cJ: class J
  let cN: class N
  let vi: setvar i
  assume axlowdimlem14.1: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )
  assume axlowdimlem14.2: |- R = ( { <. ( J + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( J + 1 ) } ) X. { 0 } ) )


  assert |- ( ( N e. NN /\ I e. ( 1 ... ( N - 1 ) ) /\ J e. ( 1 ... ( N - 1 ) ) ) -> ( Q = R -> I = J ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    cJ
    @2
    wcel
    #
    w3a
    #
    cQ
    cR
    wceq
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @7
    cR
    cfv
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    cI
    cJ
    wceq
    #
    @0
    @3
    @4
    @6
    @12
    wb
    #
    @0
    @3
    wa
    #
    cQ
    @11
    wfn
    #
    cR
    @11
    wfn
    #
    @14
    @0
    @4
    wa
    #
    @15
    @11
    cr
    cQ
    wf
    #
    @16
    @15
    cQ
    cN
    cee
    cfv
    #
    wcel
    #
    @19
    cQ
    cI
    cN
    axlowdimlem14.1
    axlowdimlem10
    @0
    @21
    @19
    wb
    @3
    cQ
    cN
    elee
    adantr
    mpbid
    @11
    cr
    cQ
    ffn
    syl
    @18
    @11
    cr
    cR
    wf
    #
    @17
    @18
    cR
    @20
    wcel
    #
    @22
    cR
    cJ
    cN
    axlowdimlem14.2
    axlowdimlem10
    @0
    @23
    @22
    wb
    @4
    cR
    cN
    elee
    adantr
    mpbid
    @11
    cr
    cR
    ffn
    syl
    vi
    @11
    cQ
    cR
    eqfnfv
    syl2an
    3impdi
    @5
    @13
    @12
    @5
    cI
    cJ
    wne
    #
    @10
    wn
    #
    vi
    @11
    wrex
    #
    @13
    wn
    @12
    wn
    @5
    @24
    @26
    @5
    @24
    wa
    #
    cI
    c1
    caddc
    co
    #
    @11
    wcel
    #
    @28
    cQ
    cfv
    #
    @28
    cR
    cfv
    #
    wne
    #
    @26
    @5
    @29
    @24
    @0
    @3
    @29
    @4
    cI
    cN
    fznatpl1
    3adant3
    adantr
    #
    @27
    c1
    cc0
    @30
    @31
    c1
    cc0
    wne
    @27
    ax-1ne0
    a1i
    @30
    c1
    wceq
    @27
    cQ
    cI
    cN
    axlowdimlem14.1
    axlowdimlem11
    a1i
    @27
    @29
    @28
    cJ
    c1
    caddc
    co
    #
    wne
    #
    @31
    cc0
    wceq
    @33
    @5
    @35
    @24
    @5
    @28
    @34
    cI
    cJ
    @3
    @4
    @28
    @34
    wceq
    @13
    wb
    #
    @0
    @3
    cI
    cc
    wcel
    #
    cJ
    cc
    wcel
    #
    @36
    @4
    @3
    cI
    cI
    c1
    @1
    elfzelz
    zcnd
    @4
    cJ
    cJ
    c1
    @1
    elfzelz
    zcnd
    @37
    @38
    c1
    cc
    wcel
    @36
    ax-1cn
    cI
    cJ
    c1
    addcan2
    mp3an3
    syl2an
    3adant1
    necon3bid
    biimpar
    cR
    cJ
    @28
    cN
    axlowdimlem14.2
    axlowdimlem12
    syl2anc
    3netr4d
    @25
    @32
    vi
    @28
    @11
    @25
    @8
    @9
    wne
    @7
    @28
    wceq
    #
    @32
    @8
    @9
    df-ne
    @39
    @8
    @30
    @9
    @31
    @7
    @28
    cQ
    fveq2
    @7
    @28
    cR
    fveq2
    neeq12d
    syl5bbr
    rspcev
    syl2anc
    ex
    cI
    cJ
    df-ne
    @10
    vi
    @11
    rexnal
    3imtr3g
    con4d
    sylbid
end
