include "cuo.mm"
include "wcel.mm"
include "clo.mm"
include "chil.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "unoplin.mm"
include "csp.mm"
include "co.mm"
include "elunop.mm"
include "simplbi.mm"
include "unopnorm.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "cid.mm"
include "cres.mm"
include "cif.mm"
include "eleq1.mm"
include "foeq1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "3anbi123d.mm"
include "idlnop.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1ofo.mm"
include "ax-mp.mm"
include "fvresi.mm"
include "rgen.mm"
include "3pm3.2i.mm"
include "elimhyp.mm"
include "simp1i.mm"
include "simp2i.mm"
include "simp3i.mm"
include "lnopunii.mm"
include "dedth.mm"
include "impbii.mm"

theorem elunop2
  let vx: setvar x
  let cT: class T
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint T x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- ( T e. UniOp <-> ( T e. LinOp /\ T : ~H -onto-> ~H /\ A. x e. ~H ( normh ` ( T ` x ) ) = ( normh ` x ) ) )

  proof
    cT
    cuo
    wcel
    #
    cT
    clo
    wcel
    #
    chil
    chil
    cT
    wfo
    #
    vx
    cv
    #
    cT
    cfv
    #
    cno
    cfv
    #
    @3
    cno
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    w3a
    #
    @0
    @1
    @2
    @8
    cT
    unoplin
    @0
    @2
    @4
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    @3
    @10
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    vx
    vy
    cT
    elunop
    simplbi
    @0
    @7
    vx
    chil
    @3
    cT
    unopnorm
    ralrimiva
    3jca
    @9
    @0
    @9
    cT
    cid
    chil
    cres
    #
    cif
    #
    cuo
    wcel
    cT
    @12
    cT
    @13
    cuo
    eleq1
    vy
    @13
    @13
    clo
    wcel
    #
    chil
    chil
    @13
    wfo
    #
    @10
    @13
    cfv
    #
    cno
    cfv
    #
    @10
    cno
    cfv
    #
    wceq
    #
    vy
    chil
    wral
    #
    @9
    @14
    @15
    @20
    w3a
    @12
    clo
    wcel
    #
    chil
    chil
    @12
    wfo
    #
    @10
    @12
    cfv
    #
    cno
    cfv
    #
    @18
    wceq
    #
    vy
    chil
    wral
    #
    w3a
    cT
    @12
    cT
    @13
    wceq
    #
    @1
    @14
    @2
    @15
    @8
    @20
    cT
    @13
    clo
    eleq1
    chil
    chil
    cT
    @13
    foeq1
    @8
    @11
    cno
    cfv
    #
    @18
    wceq
    #
    vy
    chil
    wral
    @27
    @20
    @7
    @29
    vx
    vy
    chil
    @3
    @10
    wceq
    #
    @5
    @28
    @6
    @18
    @30
    @4
    @11
    cno
    @3
    @10
    cT
    fveq2
    fveq2d
    @3
    @10
    cno
    fveq2
    eqeq12d
    cbvralv
    @27
    @29
    @19
    vy
    chil
    @27
    @28
    @17
    @18
    @27
    @11
    @16
    cno
    @10
    cT
    @13
    fveq1
    fveq2d
    eqeq1d
    ralbidv
    syl5bb
    3anbi123d
    @12
    @13
    wceq
    #
    @21
    @14
    @22
    @15
    @26
    @20
    @12
    @13
    clo
    eleq1
    chil
    chil
    @12
    @13
    foeq1
    @31
    @25
    @19
    vy
    chil
    @31
    @24
    @17
    @18
    @31
    @23
    @16
    cno
    @10
    @12
    @13
    fveq1
    fveq2d
    eqeq1d
    ralbidv
    3anbi123d
    @21
    @22
    @26
    idlnop
    chil
    chil
    @12
    wf1o
    @22
    chil
    f1oi
    chil
    chil
    @12
    f1ofo
    ax-mp
    @25
    vy
    chil
    @10
    chil
    wcel
    @23
    @10
    cno
    chil
    @10
    fvresi
    fveq2d
    rgen
    3pm3.2i
    elimhyp
    #
    simp1i
    @14
    @15
    @20
    @32
    simp2i
    @14
    @15
    @20
    @32
    simp3i
    lnopunii
    dedth
    impbii
end
