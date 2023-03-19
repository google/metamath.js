include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wcel.mm"
include "cc0.mm"
include "cioo.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "rabidim1.mm"
include "adantl.mm"
include "cxr.mm"
include "1red.mm"
include "ltned.mm"
include "redivcld.mm"
include "rexrd.mm"
include "adantr.mm"
include "0xr.mm"
include "a1i.mm"
include "cr.mm"
include "sylan2.mm"
include "rabidim2.mm"
include "wne.mm"
include "syldan.mm"
include "rereccld.mm"
include "0red.mm"
include "lttrd.mm"
include "reclt0.mm"
include "mpbird.mm"
include "ltdiv23neg.mm"
include "mpbid.mm"
include "eliood.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "ex.mm"
include "simplbi.mm"
include "simprbi.mm"
include "ioogtlbd.mm"
include "iooltubd.mm"
include "impbid.mm"
include "alrimi.mm"
include "nfrab1.mm"
include "dfcleqf.mm"

theorem pimrecltneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume pimrecltneg.x: |- F/ x ph
  assume pimrecltneg.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume pimrecltneg.n: |- ( ( ph /\ x e. A ) -> B =/= 0 )
  assume pimrecltneg.c: |- ( ph -> C e. RR )
  assume pimrecltneg.l: |- ( ph -> C < 0 )


  assert |- ( ph -> { x e. A | ( 1 / B ) < C } = { x e. A | B e. ( ( 1 / C ) (,) 0 ) } )

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
    cB
    c1
    cC
    cdiv
    co
    #
    cc0
    cioo
    co
    wcel
    #
    vx
    cA
    crab
    #
    wcel
    #
    wb
    #
    vx
    wal
    @3
    @7
    wceq
    wph
    @9
    vx
    pimrecltneg.x
    wph
    @4
    @8
    wph
    @4
    @8
    wph
    @4
    wa
    #
    @0
    cA
    wcel
    #
    @6
    wa
    @8
    @10
    @11
    @6
    @4
    @11
    wph
    @2
    vx
    cA
    rabidim1
    #
    adantl
    #
    @10
    @5
    cc0
    cB
    wph
    @5
    cxr
    wcel
    #
    @4
    wph
    @5
    wph
    c1
    cC
    wph
    1red
    #
    pimrecltneg.c
    wph
    cC
    cc0
    pimrecltneg.c
    pimrecltneg.l
    ltned
    redivcld
    rexrd
    #
    adantr
    cc0
    cxr
    wcel
    #
    @10
    0xr
    a1i
    @4
    wph
    @11
    cB
    cr
    wcel
    #
    @12
    pimrecltneg.b
    sylan2
    #
    @10
    @2
    @5
    cB
    clt
    wbr
    #
    @4
    @2
    wph
    @2
    vx
    cA
    rabidim2
    adantl
    #
    @10
    c1
    cB
    cC
    wph
    c1
    cr
    wcel
    #
    @4
    @15
    adantr
    @19
    @10
    cB
    cc0
    clt
    wbr
    @1
    cc0
    clt
    wbr
    @10
    @1
    cC
    cc0
    @10
    cB
    @19
    wph
    @4
    @11
    cB
    cc0
    wne
    @13
    pimrecltneg.n
    syldan
    #
    rereccld
    wph
    cC
    cr
    wcel
    #
    @4
    pimrecltneg.c
    adantr
    #
    @10
    0red
    @21
    wph
    cC
    cc0
    clt
    wbr
    #
    @4
    pimrecltneg.l
    adantr
    #
    lttrd
    @10
    cB
    @19
    @23
    reclt0
    mpbird
    #
    @25
    @27
    ltdiv23neg
    mpbid
    @28
    eliood
    jca
    @6
    vx
    cA
    rabid
    #
    sylibr
    ex
    wph
    @8
    @4
    wph
    @8
    wa
    #
    @11
    @2
    wa
    @4
    @30
    @11
    @2
    @8
    @11
    wph
    @8
    @11
    @6
    @29
    simplbi
    adantl
    #
    @30
    @20
    @2
    @30
    @5
    cc0
    cB
    wph
    @14
    @8
    @16
    adantr
    #
    @17
    @30
    0xr
    a1i
    #
    @8
    @6
    wph
    @8
    @11
    @6
    @29
    simprbi
    adantl
    #
    ioogtlbd
    @30
    c1
    cC
    cB
    wph
    @22
    @8
    @15
    adantr
    wph
    @24
    @8
    pimrecltneg.c
    adantr
    wph
    @26
    @8
    pimrecltneg.l
    adantr
    wph
    @8
    @11
    @18
    @31
    pimrecltneg.b
    syldan
    @30
    @5
    cc0
    cB
    @32
    @33
    @34
    iooltubd
    ltdiv23neg
    mpbid
    jca
    @2
    vx
    cA
    rabid
    sylibr
    ex
    impbid
    alrimi
    vx
    @3
    @7
    @2
    vx
    cA
    nfrab1
    @6
    vx
    cA
    nfrab1
    dfcleqf
    sylibr
end
