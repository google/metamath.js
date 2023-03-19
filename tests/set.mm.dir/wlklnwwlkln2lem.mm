include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "wwlknbp.mm"
include "cwwlks.mm"
include "c1.mm"
include "caddc.mm"
include "wb.mm"
include "iswwlksn.mm"
include "adantr.mm"
include "cmin.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "adantl.mm"
include "1cnd.mm"
include "nn0cn.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "syl6rbb.mm"
include "biimpcd.mm"
include "impcom.mm"
include "com12.mm"
include "imp.mm"
include "simpr.mm"
include "wlklenvm1.mm"
include "jccir.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "syl5ib.mm"
include "expd.mm"
include "mpcom.mm"
include "sylbid.mm"
include "3adant1.mm"

theorem wlklnwwlkln2lem
  let wph: wff ph
  let cP: class P
  let vf: setvar f
  let cG: class G
  let cN: class N
  assume wlklnwwlkln2lem.1: |- ( ph -> ( P e. ( WWalks ` G ) -> E. f f ( Walks ` G ) P ) )

  disjoint G f
  disjoint N f
  disjoint P f
  disjoint f ph
  assert |- ( ph -> ( P e. ( N WWalksN G ) -> E. f ( f ( Walks ` G ) P /\ ( # ` f ) = N ) ) )

  proof
    cP
    cN
    cG
    cwwlksn
    co
    wcel
    #
    wph
    vf
    cv
    #
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @1
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vf
    wex
    #
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cP
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    w3a
    @0
    wph
    @6
    wi
    #
    cG
    cN
    @9
    cP
    @9
    eqid
    wwlknbp
    @8
    @10
    @0
    @11
    wi
    @7
    @8
    @10
    wa
    #
    @0
    cP
    cG
    cwwlks
    cfv
    wcel
    #
    cP
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @11
    @8
    @0
    @17
    wb
    @10
    cG
    cN
    cP
    iswwlksn
    adantr
    @12
    @17
    @11
    @14
    c1
    cmin
    co
    #
    cN
    wceq
    #
    @12
    @17
    wa
    #
    @11
    @17
    @12
    @19
    @16
    @12
    @19
    wi
    @13
    @12
    @16
    @19
    @12
    @19
    @15
    @14
    wceq
    @16
    @12
    @14
    c1
    cN
    @10
    @14
    cc
    wcel
    @8
    @10
    @14
    @9
    cP
    lencl
    nn0cnd
    adantl
    @12
    1cnd
    @8
    cN
    cc
    wcel
    @10
    cN
    nn0cn
    adantr
    subadd2d
    @15
    @14
    eqcom
    syl6rbb
    biimpcd
    adantl
    impcom
    @19
    @20
    wph
    @6
    @20
    wph
    wa
    #
    @2
    @3
    @18
    wceq
    #
    wa
    #
    vf
    wex
    #
    @19
    @6
    @21
    @2
    vf
    wex
    #
    @24
    @20
    wph
    @25
    @17
    wph
    @25
    wi
    #
    @12
    @13
    @26
    @16
    wph
    @13
    @25
    wlklnwwlkln2lem.1
    com12
    adantr
    adantl
    imp
    @21
    @2
    @23
    vf
    @21
    @2
    @23
    @21
    @2
    wa
    @2
    @22
    @21
    @2
    simpr
    cP
    @1
    cG
    wlklenvm1
    jccir
    ex
    eximdv
    mpd
    @19
    @23
    @5
    vf
    @19
    @22
    @4
    @2
    @18
    cN
    @3
    eqeq2
    anbi2d
    exbidv
    syl5ib
    expd
    mpcom
    ex
    sylbid
    3adant1
    mpcom
    com12
end
