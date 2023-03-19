include "cuspgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "wral.mm"
include "wi.mm"
include "wf1.mm"
include "uspgredg2vlem.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "cbvriotav.mm"
include "cedg.mm"
include "cfv.mm"
include "w3a.mm"
include "wreu.mm"
include "simpl.mm"
include "eleq2.mm"
include "elrab2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "anim12i.mm"
include "3anass.mm"
include "sylibr.mm"
include "cvtx.mm"
include "uspgredg2vtxeu.mm"
include "wb.mm"
include "reueq1.mm"
include "ax-mp.mm"
include "syl.mm"
include "adantl.mm"
include "riotaeqimp.mm"
include "ex.mm"
include "ralrimivva.mm"
include "eqeq1.mm"
include "riotabidv.mm"
include "f1mpt.mm"
include "sylanbrc.mm"

theorem uspgredg2v
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vn: setvar n
  assume uspgredg2v.v: |- V = ( Vtx ` G )
  assume uspgredg2v.e: |- E = ( Edg ` G )
  assume uspgredg2v.a: |- A = { e e. E | N e. e }
  assume uspgredg2v.f: |- F = ( y e. A |-> ( iota_ z e. V y = { N , z } ) )

  disjoint E e
  disjoint G z
  disjoint N e
  disjoint N z
  disjoint V z
  disjoint A y
  disjoint G y
  disjoint N y
  disjoint y z
  disjoint V y
  disjoint e y
  disjoint Y e
  disjoint Y z
  disjoint A x
  disjoint x y
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint N x
  disjoint n z
  disjoint x z
  disjoint V n
  disjoint V x
  disjoint e x
  assert |- ( ( G e. USPGraph /\ N e. V ) -> F : A -1-1-> V )

  proof
    cG
    cuspgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    vy
    cv
    #
    cN
    vz
    cv
    #
    cpr
    #
    wceq
    #
    vz
    cV
    crio
    #
    cV
    wcel
    #
    vy
    cA
    wral
    #
    @7
    vx
    cv
    #
    @5
    wceq
    #
    vz
    cV
    crio
    #
    wceq
    #
    @3
    @10
    wceq
    #
    wi
    #
    vx
    cA
    wral
    vy
    cA
    wral
    cA
    cV
    cF
    wf1
    @0
    @9
    @1
    @0
    @8
    vy
    cA
    vz
    cA
    ve
    cE
    cG
    cN
    cV
    @3
    uspgredg2v.v
    uspgredg2v.e
    uspgredg2v.a
    uspgredg2vlem
    ralrimiva
    adantr
    @2
    @15
    vy
    vx
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    wa
    #
    @13
    @14
    @19
    cN
    vn
    cv
    #
    cpr
    #
    @7
    @12
    cV
    @3
    @10
    vn
    @6
    @3
    @21
    wceq
    #
    vz
    vn
    cV
    @4
    @20
    wceq
    #
    @5
    @21
    @3
    @4
    @20
    cN
    preq2
    #
    eqeq2d
    cbvriotav
    @11
    @10
    @21
    wceq
    #
    vz
    vn
    cV
    @23
    @5
    @21
    @10
    @24
    eqeq2d
    cbvriotav
    @19
    @0
    @3
    cG
    cedg
    cfv
    #
    wcel
    #
    cN
    @3
    wcel
    #
    w3a
    #
    @22
    vn
    cV
    wreu
    #
    @19
    @0
    @27
    @28
    wa
    #
    wa
    @29
    @2
    @0
    @18
    @31
    @0
    @1
    simpl
    #
    @16
    @31
    @17
    @16
    @3
    cE
    wcel
    #
    @28
    wa
    @31
    cN
    ve
    cv
    #
    wcel
    #
    @28
    ve
    @3
    cE
    cA
    @34
    @3
    cN
    eleq2
    uspgredg2v.a
    elrab2
    @33
    @27
    @28
    @33
    @27
    cE
    @26
    @3
    uspgredg2v.e
    eleq2i
    biimpi
    anim1i
    sylbi
    adantr
    anim12i
    @0
    @27
    @28
    3anass
    sylibr
    @29
    @22
    vn
    cG
    cvtx
    cfv
    #
    wreu
    #
    @30
    vn
    @3
    cG
    cN
    uspgredg2vtxeu
    cV
    @36
    wceq
    #
    @30
    @37
    wb
    uspgredg2v.v
    @22
    vn
    cV
    @36
    reueq1
    ax-mp
    sylibr
    syl
    @19
    @0
    @10
    @26
    wcel
    #
    cN
    @10
    wcel
    #
    w3a
    #
    @25
    vn
    cV
    wreu
    #
    @19
    @0
    @39
    @40
    wa
    #
    wa
    @41
    @2
    @0
    @18
    @43
    @32
    @17
    @43
    @16
    @17
    @10
    cE
    wcel
    #
    @40
    wa
    @43
    @35
    @40
    ve
    @10
    cE
    cA
    @34
    @10
    cN
    eleq2
    uspgredg2v.a
    elrab2
    @44
    @39
    @40
    @44
    @39
    cE
    @26
    @10
    uspgredg2v.e
    eleq2i
    biimpi
    anim1i
    sylbi
    adantl
    anim12i
    @0
    @39
    @40
    3anass
    sylibr
    @41
    @25
    vn
    @36
    wreu
    #
    @42
    vn
    @10
    cG
    cN
    uspgredg2vtxeu
    @38
    @42
    @45
    wb
    uspgredg2v.v
    @25
    vn
    cV
    @36
    reueq1
    ax-mp
    sylibr
    syl
    riotaeqimp
    ex
    ralrimivva
    vy
    vx
    cA
    cV
    @7
    @12
    cF
    uspgredg2v.f
    @14
    @6
    @11
    vz
    cV
    @3
    @10
    @5
    eqeq1
    riotabidv
    f1mpt
    sylanbrc
end
