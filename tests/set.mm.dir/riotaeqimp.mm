include "wceq.mm"
include "wa.mm"
include "crio.mm"
include "csb.mm"
include "wb.mm"
include "eqcomi.mm"
include "eqeq2i.mm"
include "a1i.mm"
include "bicomd.mm"
include "biimpa.mm"
include "eqeq1i.mm"
include "wcel.mm"
include "wreu.mm"
include "riotacl.mm"
include "syl.mm"
include "syl5eqel.mm"
include "nfv.mm"
include "nfcvd.mm"
include "nfcsb1d.mm"
include "nfeqd.mm"
include "id.mm"
include "cv.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "riota2df.mm"
include "syl2anc.mm"
include "syl5bb.mm"
include "wi.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantr.mm"
include "csbeq1.mm"
include "eqcoms.mm"
include "eqeq12.mm"
include "ancoms.mm"
include "syl5ibrcom.mm"
include "expd.mm"
include "sylbird.mm"
include "mp2d.mm"

theorem riotaeqimp
  let wph: wff ph
  let cA: class A
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume riotaeqimp.i: |- I = ( iota_ a e. V X = A )
  assume riotaeqimp.j: |- J = ( iota_ a e. V Y = A )
  assume riotaeqimp.x: |- ( ph -> E! a e. V X = A )
  assume riotaeqimp.y: |- ( ph -> E! a e. V Y = A )

  disjoint I a
  disjoint J a
  disjoint V a
  disjoint X a
  disjoint Y a
  assert |- ( ( ph /\ I = J ) -> X = Y )

  proof
    wph
    cI
    cJ
    wceq
    #
    wa
    #
    cI
    cY
    cA
    wceq
    #
    va
    cV
    crio
    #
    wceq
    #
    cX
    va
    cJ
    cA
    csb
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wph
    @0
    @4
    wph
    @4
    @0
    @4
    @0
    wb
    wph
    @3
    cJ
    cI
    cJ
    @3
    riotaeqimp.j
    eqcomi
    eqeq2i
    a1i
    bicomd
    biimpa
    wph
    @0
    @6
    @0
    cX
    cA
    wceq
    #
    va
    cV
    crio
    #
    cJ
    wceq
    #
    wph
    @6
    cI
    @9
    cJ
    riotaeqimp.i
    eqeq1i
    wph
    cJ
    cV
    wcel
    #
    @8
    va
    cV
    wreu
    #
    @10
    @6
    wb
    wph
    cJ
    @3
    cV
    riotaeqimp.j
    wph
    @2
    va
    cV
    wreu
    #
    @3
    cV
    wcel
    riotaeqimp.y
    @2
    va
    cV
    riotacl
    syl
    syl5eqel
    riotaeqimp.x
    @11
    @12
    wa
    @6
    @10
    @11
    @8
    @6
    va
    cV
    cJ
    @11
    va
    nfv
    @11
    va
    cJ
    nfcvd
    #
    @11
    va
    cX
    @5
    @11
    va
    cX
    nfcvd
    @11
    va
    cJ
    cA
    @14
    nfcsb1d
    nfeqd
    @11
    id
    va
    cv
    #
    cJ
    wceq
    #
    @8
    @6
    wb
    @11
    @16
    cA
    @5
    cX
    va
    cJ
    cA
    csbeq1a
    eqeq2d
    adantl
    riota2df
    bicomd
    syl2anc
    syl5bb
    biimpa
    @1
    @4
    cY
    va
    cI
    cA
    csb
    #
    wceq
    #
    @6
    @7
    wi
    #
    wph
    @18
    @4
    wb
    @0
    wph
    @18
    @3
    cI
    wceq
    #
    @4
    wph
    cI
    cV
    wcel
    #
    @13
    @18
    @20
    wb
    wph
    cI
    @9
    cV
    riotaeqimp.i
    wph
    @12
    @9
    cV
    wcel
    riotaeqimp.x
    @8
    va
    cV
    riotacl
    syl
    syl5eqel
    riotaeqimp.y
    @21
    @2
    @18
    va
    cV
    cI
    @21
    va
    nfv
    @21
    va
    cI
    nfcvd
    #
    @21
    va
    cY
    @17
    @21
    va
    cY
    nfcvd
    @21
    va
    cI
    cA
    @22
    nfcsb1d
    nfeqd
    @21
    id
    @15
    cI
    wceq
    #
    @2
    @18
    wb
    @21
    @23
    cA
    @17
    cY
    va
    cI
    cA
    csbeq1a
    eqeq2d
    adantl
    riota2df
    syl2anc
    @3
    cI
    eqcom
    syl6bb
    adantr
    @0
    @18
    @19
    wi
    wph
    @0
    @18
    @6
    @7
    @0
    @7
    @18
    @6
    wa
    @5
    @17
    wceq
    #
    @24
    cJ
    cI
    va
    cJ
    cI
    cA
    csbeq1
    eqcoms
    @6
    @18
    @7
    @24
    wb
    cX
    @5
    cY
    @17
    eqeq12
    ancoms
    syl5ibrcom
    expd
    adantl
    sylbird
    mp2d
end
