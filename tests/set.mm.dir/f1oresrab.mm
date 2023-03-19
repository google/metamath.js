include "crab.mm"
include "ccnv.mm"
include "cres.mm"
include "wf1o.mm"
include "wfun.mm"
include "f1ofun.mm"
include "funcnvcnv.mm"
include "3syl.mm"
include "cima.mm"
include "wf1.mm"
include "wss.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "ssrab2.mm"
include "f1ores.mm"
include "sylancl.mm"
include "wceq.mm"
include "wb.mm"
include "wcel.mm"
include "mptpreima.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "3expia.mm"
include "alrimiv.mm"
include "wf.mm"
include "wral.mm"
include "f1of.mm"
include "syl.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "elrab3t.mm"
include "syl2anc.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "f1orescnv.mm"
include "rescnvcnv.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem f1oresrab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume f1oresrab.1: |- F = ( x e. A |-> C )
  assume f1oresrab.2: |- ( ph -> F : A -1-1-onto-> B )
  assume f1oresrab.3: |- ( ( ph /\ x e. A /\ y = C ) -> ( ch <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  assert |- ( ph -> ( F |` { x e. A | ps } ) : { x e. A | ps } -1-1-onto-> { y e. B | ch } )

  proof
    wph
    wps
    vx
    cA
    crab
    #
    wch
    vy
    cB
    crab
    #
    cF
    ccnv
    #
    ccnv
    #
    @0
    cres
    #
    wf1o
    #
    @0
    @1
    cF
    @0
    cres
    #
    wf1o
    #
    wph
    @3
    wfun
    #
    @1
    @0
    @2
    @1
    cres
    #
    wf1o
    #
    @5
    wph
    cA
    cB
    cF
    wf1o
    #
    cF
    wfun
    @8
    f1oresrab.2
    cA
    cB
    cF
    f1ofun
    cF
    funcnvcnv
    3syl
    wph
    @1
    @2
    @1
    cima
    #
    @9
    wf1o
    #
    @10
    wph
    cB
    cA
    @2
    wf1
    #
    @1
    cB
    wss
    @13
    wph
    @11
    cB
    cA
    @2
    wf1o
    @14
    f1oresrab.2
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @2
    f1of1
    3syl
    wch
    vy
    cB
    ssrab2
    cB
    cA
    @1
    @2
    f1ores
    sylancl
    wph
    @12
    @0
    wceq
    @13
    @10
    wb
    wph
    @12
    cC
    @1
    wcel
    #
    vx
    cA
    crab
    @0
    vx
    cA
    cC
    @1
    cF
    f1oresrab.1
    mptpreima
    wph
    @15
    wps
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vy
    cv
    cC
    wceq
    #
    wch
    wps
    wb
    #
    wi
    #
    vy
    wal
    cC
    cB
    wcel
    #
    @15
    wps
    wb
    @17
    @20
    vy
    wph
    @16
    @18
    @19
    f1oresrab.3
    3expia
    alrimiv
    wph
    @21
    vx
    cA
    wph
    cA
    cB
    cF
    wf
    #
    @21
    vx
    cA
    wral
    wph
    @11
    @22
    f1oresrab.2
    cA
    cB
    cF
    f1of
    syl
    vx
    cA
    cB
    cC
    cF
    f1oresrab.1
    fmpt
    sylibr
    r19.21bi
    wch
    wps
    vy
    cC
    cB
    elrab3t
    syl2anc
    rabbidva
    syl5eq
    @12
    @0
    @1
    @9
    f1oeq3
    syl
    mpbid
    @0
    @1
    @2
    f1orescnv
    syl2anc
    @4
    @6
    wceq
    @5
    @7
    wb
    cF
    @0
    rescnvcnv
    @0
    @1
    @4
    @6
    f1oeq1
    ax-mp
    sylib
end
