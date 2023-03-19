include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "cc0.mm"
include "ltned.mm"
include "redivcld.mm"
include "ltmulneg.mm"
include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "recn.mm"
include "syl.mm"
include "divcan1d.mm"
include "breq2d.mm"
include "c1.mm"
include "remulcl.mm"
include "syl2anc.mm"
include "rereccld.mm"
include "reclt0d.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "mulcld.mm"
include "wne.mm"
include "wceq.mm"
include "divcan3.mm"
include "3expb.mm"
include "syl12anc.mm"
include "eqtr3d.mm"
include "breq12d.mm"
include "bitrd.mm"
include "3bitrd.mm"

theorem ltdiv23neg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltdiv23neg.1: |- ( ph -> A e. RR )
  assume ltdiv23neg.2: |- ( ph -> B e. RR )
  assume ltdiv23neg.3: |- ( ph -> B < 0 )
  assume ltdiv23neg.4: |- ( ph -> C e. RR )
  assume ltdiv23neg.5: |- ( ph -> C < 0 )


  assert |- ( ph -> ( ( A / B ) < C <-> ( A / C ) < B ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    #
    cC
    clt
    wbr
    cC
    cB
    cmul
    co
    #
    @0
    cB
    cmul
    co
    #
    clt
    wbr
    @1
    cA
    clt
    wbr
    #
    cA
    cC
    cdiv
    co
    #
    cB
    clt
    wbr
    #
    wph
    @0
    cC
    cB
    wph
    cA
    cB
    ltdiv23neg.1
    ltdiv23neg.2
    wph
    cB
    cc0
    ltdiv23neg.2
    ltdiv23neg.3
    ltned
    #
    redivcld
    ltdiv23neg.4
    ltdiv23neg.2
    ltdiv23neg.3
    ltmulneg
    wph
    @2
    cA
    @1
    clt
    wph
    cA
    cB
    wph
    cA
    cr
    wcel
    cA
    cc
    wcel
    ltdiv23neg.1
    cA
    recn
    syl
    #
    wph
    cB
    cr
    wcel
    #
    cB
    cc
    wcel
    #
    ltdiv23neg.2
    cB
    recn
    syl
    #
    @6
    divcan1d
    breq2d
    wph
    @3
    cA
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    @1
    @11
    cmul
    co
    #
    clt
    wbr
    @5
    wph
    @1
    cA
    @11
    wph
    cC
    cr
    wcel
    #
    @8
    @1
    cr
    wcel
    ltdiv23neg.4
    ltdiv23neg.2
    cC
    cB
    remulcl
    syl2anc
    ltdiv23neg.1
    wph
    cC
    ltdiv23neg.4
    wph
    cC
    cc0
    ltdiv23neg.4
    ltdiv23neg.5
    ltned
    #
    rereccld
    wph
    cC
    ltdiv23neg.4
    ltdiv23neg.5
    reclt0d
    ltmulneg
    wph
    @12
    @4
    @13
    cB
    clt
    wph
    @4
    @12
    wph
    cA
    cC
    @7
    wph
    @14
    cC
    cc
    wcel
    #
    ltdiv23neg.4
    cC
    recn
    syl
    #
    @15
    divrecd
    eqcomd
    wph
    @1
    cC
    cdiv
    co
    #
    @13
    cB
    wph
    @1
    cC
    wph
    cC
    cB
    @17
    @10
    mulcld
    @17
    @15
    divrecd
    wph
    @9
    @16
    cC
    cc0
    wne
    #
    @18
    cB
    wceq
    #
    @10
    @17
    @15
    @9
    @16
    @19
    @20
    cB
    cC
    divcan3
    3expb
    syl12anc
    eqtr3d
    breq12d
    bitrd
    3bitrd
end
