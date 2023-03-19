include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "elintrabg.mm"
include "df-ral.mm"
include "syl6bb.mm"
include "wss.mm"
include "selpw.mm"
include "19.23v.mm"
include "bicomi.mm"
include "imbi12i.mm"
include "19.21v.mm"
include "bi2.04.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "3bitr2i.mm"
include "alcom.mm"
include "sseq1.mm"
include "eleq2.mm"
include "sseli.mm"
include "pm4.71ri.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "ceqsalv.mm"
include "wb.mm"
include "pm5.5.mm"
include "ax-mp.mm"
include "jcab.mm"
include "3bitri.mm"
include "19.26.mm"
include "anbi1i.mm"

theorem elmapintrab
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume elmapintrab.ex: |- C e. _V
  assume elmapintrab.sub: |- C C_ B

  disjoint ph w
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint B w
  disjoint B x
  disjoint C w
  assert |- ( A e. V -> ( A e. |^| { w e. ~P B | E. x ( w = C /\ ph ) } <-> ( ( E. x ph -> A e. B ) /\ A. x ( ph -> A e. C ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    vw
    cv
    #
    cC
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    vw
    cB
    cpw
    #
    crab
    cint
    wcel
    #
    @1
    @5
    wcel
    #
    @4
    cA
    @1
    wcel
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    wph
    vx
    wex
    cA
    cB
    wcel
    #
    wi
    #
    wph
    cA
    cC
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @0
    @6
    @9
    vw
    @5
    wral
    @11
    @4
    vw
    cA
    @5
    cV
    elintrabg
    @9
    vw
    @5
    df-ral
    syl6bb
    @11
    @2
    wph
    @1
    cB
    wss
    #
    @8
    wi
    #
    wi
    #
    wi
    #
    vx
    wal
    #
    vw
    wal
    @21
    vw
    wal
    #
    vx
    wal
    #
    @17
    @10
    @22
    vw
    @10
    @18
    @3
    @8
    wi
    #
    vx
    wal
    #
    wi
    @18
    @25
    wi
    #
    vx
    wal
    @22
    @7
    @18
    @9
    @26
    vw
    cB
    selpw
    @26
    @9
    @3
    @8
    vx
    19.23v
    bicomi
    imbi12i
    @18
    @25
    vx
    19.21v
    @27
    @21
    vx
    @27
    @3
    @19
    wi
    @21
    @18
    @3
    @8
    bi2.04
    @2
    wph
    @19
    impexp
    bitri
    albii
    3bitr2i
    albii
    @21
    vw
    vx
    alcom
    @24
    wph
    @12
    wi
    #
    @15
    wa
    #
    vx
    wal
    @28
    vx
    wal
    #
    @16
    wa
    @17
    @23
    @29
    vx
    @23
    wph
    cC
    cB
    wss
    #
    @12
    @14
    wa
    #
    wi
    #
    wi
    #
    @31
    wph
    @32
    wi
    #
    wi
    #
    @29
    @20
    @34
    vw
    cC
    elmapintrab.ex
    @2
    @19
    @33
    wph
    @2
    @18
    @31
    @8
    @32
    @1
    cC
    cB
    sseq1
    @2
    @8
    @14
    @32
    @1
    cC
    cA
    eleq2
    @14
    @12
    cC
    cB
    cA
    elmapintrab.sub
    sseli
    pm4.71ri
    syl6bb
    imbi12d
    imbi2d
    ceqsalv
    wph
    @31
    @32
    bi2.04
    @36
    @35
    @29
    @31
    @36
    @35
    wb
    elmapintrab.sub
    @31
    @35
    pm5.5
    ax-mp
    wph
    @12
    @14
    jcab
    bitri
    3bitri
    albii
    @28
    @15
    vx
    19.26
    @30
    @13
    @16
    wph
    @12
    vx
    19.23v
    anbi1i
    3bitri
    3bitri
    syl6bb
end
