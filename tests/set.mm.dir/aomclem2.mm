include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "cdm.mm"
include "cr1.mm"
include "cpw.mm"
include "w3a.mm"
include "csup.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "con0.mm"
include "wa.mm"
include "jca.mm"
include "r1ord3.mm"
include "sylc.mm"
include "sspwb.mm"
include "sylib.mm"
include "sseld.mm"
include "rsp.mm"
include "sylsyld.mm"
include "3imp.mm"
include "eldifad.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "syl.mm"
include "wor.mm"
include "aomclem1.mm"
include "3ad2ant1.mm"
include "inss2.mm"
include "sseldi.mm"
include "eldifsni.mm"
include "elpwi.mm"
include "3ad2ant2.mm"
include "sstrd.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "fvmpt2.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "ralrimiv.mm"

theorem aomclem2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem2.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem2.c: |- C = ( a e. _V |-> sup ( ( y ` a ) , ( R1 ` dom z ) , B ) )
  assume aomclem2.on: |- ( ph -> dom z e. On )
  assume aomclem2.su: |- ( ph -> dom z = suc U. dom z )
  assume aomclem2.we: |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) )
  assume aomclem2.a: |- ( ph -> A e. On )
  assume aomclem2.za: |- ( ph -> dom z C_ A )
  assume aomclem2.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

  disjoint y z
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a ph
  assert |- ( ph -> A. a e. ~P ( R1 ` dom z ) ( a =/= (/) -> ( C ` a ) e. a ) )

  proof
    wph
    va
    cv
    #
    c0
    wne
    #
    @0
    cC
    cfv
    #
    @0
    wcel
    #
    wi
    va
    vz
    cv
    cdm
    #
    cr1
    cfv
    #
    cpw
    #
    wph
    @0
    @6
    wcel
    #
    @1
    @3
    wph
    @7
    @1
    w3a
    #
    @2
    @0
    vy
    cv
    cfv
    #
    @5
    cB
    csup
    #
    @0
    @8
    @0
    cvv
    wcel
    @10
    @0
    wcel
    @2
    @10
    wceq
    va
    vex
    @8
    @9
    @0
    @10
    @8
    @9
    @0
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    @9
    @0
    wss
    @8
    @9
    @12
    c0
    csn
    #
    wph
    @7
    @1
    @9
    @12
    @14
    cdif
    wcel
    #
    wph
    @1
    @15
    wi
    #
    va
    cA
    cr1
    cfv
    #
    cpw
    #
    wral
    @7
    @0
    @18
    wcel
    @16
    aomclem2.y
    wph
    @6
    @18
    @0
    wph
    @5
    @17
    wss
    #
    @6
    @18
    wss
    wph
    @4
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    wa
    @4
    cA
    wss
    @19
    wph
    @20
    @21
    aomclem2.on
    aomclem2.a
    jca
    aomclem2.za
    @4
    cA
    r1ord3
    sylc
    @5
    @17
    sspwb
    sylib
    sseld
    @16
    va
    @18
    rsp
    sylsyld
    3imp
    #
    eldifad
    #
    @13
    @9
    @0
    @12
    @11
    @9
    @11
    cfn
    inss1
    sseli
    elpwid
    syl
    #
    @8
    @5
    cB
    wor
    #
    @9
    cfn
    wcel
    @9
    c0
    wne
    #
    @9
    @5
    wss
    @10
    @9
    wcel
    wph
    @7
    @25
    @1
    wph
    vz
    cB
    va
    vb
    vc
    vd
    aomclem2.b
    aomclem2.on
    aomclem2.su
    aomclem2.we
    aomclem1
    3ad2ant1
    @8
    @12
    cfn
    @9
    @11
    cfn
    inss2
    @23
    sseldi
    @8
    @15
    @26
    @22
    @9
    @12
    c0
    eldifsni
    syl
    @8
    @9
    @0
    @5
    @24
    @7
    wph
    @0
    @5
    wss
    @1
    @0
    @5
    elpwi
    3ad2ant2
    sstrd
    @5
    @9
    cB
    fisupcl
    syl13anc
    sseldd
    #
    va
    cvv
    @10
    @0
    cC
    aomclem2.c
    fvmpt2
    sylancr
    @27
    eqeltrd
    3exp
    ralrimiv
end
