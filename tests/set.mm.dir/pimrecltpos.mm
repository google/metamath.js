include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wcel.mm"
include "cc0.mm"
include "cun.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "rabidim1.mm"
include "adantr.mm"
include "simpr.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "elun2.mm"
include "syl.mm"
include "adantll.mm"
include "wn.mm"
include "0red.mm"
include "cr.mm"
include "sylan2.mm"
include "wne.mm"
include "adantl.mm"
include "necomd.mm"
include "syldan.mm"
include "lttri5d.mm"
include "elrpd.mm"
include "crp.mm"
include "ad2antrr.mm"
include "rabidim2.mm"
include "ad2antlr.mm"
include "ltrec1d.mm"
include "elun1.mm"
include "pm2.61dan.mm"
include "ex.mm"
include "simplbi.mm"
include "rprecred.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "recgt0d.mm"
include "simprbi.mm"
include "lttrd.mm"
include "adantlr.mm"
include "simpll.mm"
include "elunnel1.mm"
include "rereccld.mm"
include "reclt0d.mm"
include "syl2anc.mm"
include "impbid.mm"
include "alrimi.mm"
include "nfrab1.mm"
include "nfun.mm"
include "dfcleqf.mm"

theorem pimrecltpos
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume pimrecltpos.x: |- F/ x ph
  assume pimrecltpos.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume pimrecltpos.n: |- ( ( ph /\ x e. A ) -> B =/= 0 )
  assume pimrecltpos.c: |- ( ph -> C e. RR+ )


  assert |- ( ph -> { x e. A | ( 1 / B ) < C } = ( { x e. A | ( 1 / C ) < B } u. { x e. A | B < 0 } ) )

  proof
    wph
    vx
    cv
    #
    c1
    cB
    cdiv
    co
    #
    cC
    clt
    wbr
    #
    vx
    cA
    crab
    #
    wcel
    #
    @0
    c1
    cC
    cdiv
    co
    #
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cB
    cc0
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cun
    #
    wcel
    #
    wb
    #
    vx
    wal
    @3
    @10
    wceq
    wph
    @12
    vx
    pimrecltpos.x
    wph
    @4
    @11
    wph
    @4
    @11
    wph
    @4
    wa
    #
    @8
    @11
    @4
    @8
    @11
    wph
    @4
    @8
    wa
    #
    @0
    @9
    wcel
    #
    @11
    @14
    @0
    cA
    wcel
    #
    @8
    wa
    @15
    @14
    @16
    @8
    @4
    @16
    @8
    @2
    vx
    cA
    rabidim1
    #
    adantr
    @4
    @8
    simpr
    jca
    @8
    vx
    cA
    rabid
    #
    sylibr
    @0
    @9
    @7
    elun2
    syl
    adantll
    @13
    @8
    wn
    #
    cc0
    cB
    clt
    wbr
    #
    @11
    @13
    @19
    wa
    #
    cc0
    cB
    @21
    0red
    @13
    cB
    cr
    wcel
    #
    @19
    @4
    wph
    @16
    @22
    @17
    pimrecltpos.b
    sylan2
    #
    adantr
    @13
    cc0
    cB
    wne
    #
    @19
    wph
    @4
    @16
    @24
    @4
    @16
    wph
    @17
    adantl
    #
    wph
    @16
    wa
    #
    cB
    cc0
    pimrecltpos.n
    necomd
    syldan
    adantr
    @13
    @19
    simpr
    lttri5d
    @13
    @20
    wa
    #
    @0
    @7
    wcel
    #
    @11
    @27
    @16
    @6
    wa
    @28
    @27
    @16
    @6
    @13
    @16
    @20
    @25
    adantr
    @27
    cB
    cC
    @27
    cB
    @13
    @22
    @20
    @23
    adantr
    @13
    @20
    simpr
    elrpd
    wph
    cC
    crp
    wcel
    #
    @4
    @20
    pimrecltpos.c
    ad2antrr
    @4
    @2
    wph
    @20
    @2
    vx
    cA
    rabidim2
    ad2antlr
    ltrec1d
    jca
    @6
    vx
    cA
    rabid
    #
    sylibr
    @0
    @7
    @9
    elun1
    syl
    syldan
    pm2.61dan
    ex
    wph
    @11
    @4
    wph
    @11
    wa
    #
    @28
    @4
    wph
    @28
    @4
    @11
    wph
    @28
    wa
    #
    @16
    @2
    wa
    #
    @4
    @32
    @16
    @2
    @28
    @16
    wph
    @28
    @16
    @6
    @30
    simplbi
    adantl
    #
    @32
    cC
    cB
    wph
    @29
    @28
    pimrecltpos.c
    adantr
    #
    @32
    cB
    wph
    @28
    @16
    @22
    @34
    pimrecltpos.b
    syldan
    #
    @32
    cc0
    @5
    cB
    @32
    0red
    @32
    cC
    @35
    rprecred
    @36
    wph
    cc0
    @5
    clt
    wbr
    @28
    wph
    cC
    wph
    cC
    pimrecltpos.c
    rpred
    #
    wph
    cC
    pimrecltpos.c
    rpgt0d
    #
    recgt0d
    adantr
    @28
    @6
    wph
    @28
    @16
    @6
    @30
    simprbi
    adantl
    #
    lttrd
    elrpd
    @39
    ltrec1d
    jca
    @2
    vx
    cA
    rabid
    #
    sylibr
    adantlr
    @31
    @28
    wn
    #
    wa
    wph
    @15
    @4
    wph
    @11
    @41
    simpll
    @11
    @41
    @15
    wph
    @0
    @7
    @9
    elunnel1
    adantll
    wph
    @15
    wa
    #
    @33
    @4
    @42
    @16
    @2
    @15
    @16
    wph
    @15
    @16
    @8
    @18
    simplbi
    adantl
    #
    @42
    @1
    cc0
    cC
    wph
    @15
    @16
    @1
    cr
    wcel
    @43
    @26
    cB
    pimrecltpos.b
    pimrecltpos.n
    rereccld
    syldan
    @42
    0red
    wph
    cC
    cr
    wcel
    @15
    @37
    adantr
    @42
    cB
    wph
    @15
    @16
    @22
    @43
    pimrecltpos.b
    syldan
    @15
    @8
    wph
    @15
    @16
    @8
    @18
    simprbi
    adantl
    reclt0d
    wph
    cc0
    cC
    clt
    wbr
    @15
    @38
    adantr
    lttrd
    jca
    @40
    sylibr
    syl2anc
    pm2.61dan
    ex
    impbid
    alrimi
    vx
    @3
    @10
    @2
    vx
    cA
    nfrab1
    vx
    @7
    @9
    @6
    vx
    cA
    nfrab1
    @8
    vx
    cA
    nfrab1
    nfun
    dfcleqf
    sylibr
end
