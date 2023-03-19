include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "bnj1211.mm"
include "wne.mm"
include "wa.mm"
include "rabeq2i.mm"
include "notbii.mm"
include "imnan.mm"
include "nne.mm"
include "imbi2i.mm"
include "3bitr2i.mm"
include "sseli.mm"
include "imim1i.mm"
include "ax-1.mm"
include "anim1i.mm"
include "simpr.mm"
include "simpl.mm"
include "mpd.mm"
include "jca.mm"
include "impbii.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitr3i.mm"
include "mpbi.mm"
include "sylbi.mm"
include "sylg.mm"
include "bnj1142.mm"

theorem bnj1533
  let wth: wff th
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume bnj1533.1: |- ( th -> A. z e. B -. z e. D )
  assume bnj1533.2: |- B C_ A
  assume bnj1533.3: |- D = { z e. A | C =/= E }


  assert |- ( th -> A. z e. B C = E )

  proof
    wth
    cC
    cE
    wceq
    #
    vz
    cB
    wth
    vz
    cv
    #
    cB
    wcel
    #
    @1
    cD
    wcel
    #
    wn
    #
    wi
    #
    @2
    @0
    wi
    #
    vz
    wth
    @4
    vz
    cB
    bnj1533.1
    bnj1211
    @5
    @2
    @1
    cA
    wcel
    #
    @0
    wi
    #
    wi
    #
    @6
    @4
    @8
    @2
    @4
    @7
    cC
    cE
    wne
    #
    wa
    #
    wn
    @7
    @10
    wn
    #
    wi
    @8
    @3
    @11
    @10
    vz
    cD
    cA
    bnj1533.3
    rabeq2i
    notbii
    @7
    @10
    imnan
    @12
    @0
    @7
    cC
    cE
    nne
    imbi2i
    3bitr2i
    imbi2i
    @8
    @6
    wi
    #
    @9
    @6
    wi
    #
    @2
    @7
    @0
    cB
    cA
    @1
    bnj1533.2
    sseli
    imim1i
    @8
    @2
    wa
    #
    @0
    wi
    @9
    @2
    wa
    #
    @0
    wi
    @13
    @14
    @15
    @16
    @0
    @15
    @16
    @8
    @9
    @2
    @8
    @2
    ax-1
    anim1i
    @16
    @8
    @2
    @16
    @2
    @8
    @9
    @2
    simpr
    #
    @9
    @2
    simpl
    mpd
    @17
    jca
    impbii
    imbi1i
    @8
    @2
    @0
    impexp
    @9
    @2
    @0
    impexp
    3bitr3i
    mpbi
    sylbi
    sylg
    bnj1142
end
