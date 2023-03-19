include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cc0.mm"
include "cfv.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "wcel.mm"
include "w3a.mm"
include "crio.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "cbvriotav.mm"
include "eqtri.mm"
include "wreu.mm"
include "ccvm.mm"
include "cvmlift.mm"
include "syl22anc.mm"
include "riotacl2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem cvmliftiota
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vg: setvar g
  assume cvmliftiota.b: |- B = U. C
  assume cvmliftiota.h: |- H = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) )
  assume cvmliftiota.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftiota.g: |- ( ph -> G e. ( II Cn J ) )
  assume cvmliftiota.p: |- ( ph -> P e. B )
  assume cvmliftiota.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )

  disjoint C f
  disjoint F f
  disjoint G f
  disjoint P f
  disjoint B g
  disjoint f g
  disjoint C g
  disjoint F g
  disjoint G g
  disjoint H g
  disjoint P g
  disjoint J g
  assert |- ( ph -> ( H e. ( II Cn C ) /\ ( F o. H ) = G /\ ( H ` 0 ) = P ) )

  proof
    wph
    cH
    cF
    vg
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cc0
    @0
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    cii
    cC
    ccn
    co
    #
    crab
    #
    wcel
    #
    cH
    @6
    wcel
    #
    cF
    cH
    ccom
    #
    cG
    wceq
    #
    cc0
    cH
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    wph
    cH
    @5
    vg
    @6
    crio
    #
    @7
    cH
    cF
    vf
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cc0
    @16
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vf
    @6
    crio
    @15
    cvmliftiota.h
    @21
    @5
    vf
    vg
    @6
    @16
    @0
    wceq
    #
    @18
    @2
    @20
    @4
    @22
    @17
    @1
    cG
    @16
    @0
    cF
    coeq2
    eqeq1d
    @22
    @19
    @3
    cP
    cc0
    @16
    @0
    fveq1
    eqeq1d
    anbi12d
    cbvriotav
    eqtri
    wph
    @5
    vg
    @6
    wreu
    #
    @15
    @7
    wcel
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    cG
    cii
    cJ
    ccn
    co
    wcel
    cP
    cB
    wcel
    cP
    cF
    cfv
    cc0
    cG
    cfv
    wceq
    @23
    cvmliftiota.f
    cvmliftiota.g
    cvmliftiota.p
    cvmliftiota.e
    cB
    cC
    cP
    vg
    cF
    cG
    cJ
    cvmliftiota.b
    cvmlift
    syl22anc
    @5
    vg
    @6
    riotacl2
    syl
    syl5eqel
    @8
    @9
    @11
    @13
    wa
    #
    wa
    @14
    @5
    @24
    vg
    cH
    @6
    @0
    cH
    wceq
    #
    @2
    @11
    @4
    @13
    @25
    @1
    @10
    cG
    @0
    cH
    cF
    coeq2
    eqeq1d
    @25
    @3
    @12
    cP
    cc0
    @0
    cH
    fveq1
    eqeq1d
    anbi12d
    elrab
    @9
    @11
    @13
    3anass
    bitr4i
    sylib
end
