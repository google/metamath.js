include "cv.mm"
include "cdm.mm"
include "cr1.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "cif.mm"
include "cxp.mm"
include "cin.mm"
include "wwe.mm"
include "wa.mm"
include "con0.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "wral.mm"
include "aomclem4.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqidd.mm"
include "weeq12d.mm"
include "mpbird.mm"
include "wn.mm"
include "csuc.mm"
include "word.mm"
include "wo.mm"
include "eloni.mm"
include "orduniorsuc.mm"
include "3syl.mm"
include "orcanai.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "cfn.mm"
include "csn.mm"
include "cdif.mm"
include "wi.mm"
include "aomclem3.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "weinxp.mm"
include "sylib.mm"
include "wb.mm"
include "weeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem aomclem5
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem5.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem5.c: |- C = ( a e. _V |-> sup ( ( y ` a ) , ( R1 ` dom z ) , B ) )
  assume aomclem5.d: |- D = recs ( ( a e. _V |-> ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) )
  assume aomclem5.e: |- E = { <. a , b >. | |^| ( `' D " { a } ) e. |^| ( `' D " { b } ) }
  assume aomclem5.f: |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/ ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) }
  assume aomclem5.g: |- G = ( if ( dom z = U. dom z , F , E ) i^i ( ( R1 ` dom z ) X. ( R1 ` dom z ) ) )
  assume aomclem5.on: |- ( ph -> dom z e. On )
  assume aomclem5.we: |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) )
  assume aomclem5.a: |- ( ph -> A e. On )
  assume aomclem5.za: |- ( ph -> dom z C_ A )
  assume aomclem5.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

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
  disjoint b ph
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  assert |- ( ph -> G We ( R1 ` dom z ) )

  proof
    wph
    vz
    cv
    #
    cdm
    #
    cr1
    cfv
    #
    @1
    @1
    cuni
    #
    wceq
    #
    cF
    cE
    cif
    #
    @2
    @2
    cxp
    cin
    #
    wwe
    #
    @2
    cG
    wwe
    #
    wph
    @2
    @5
    wwe
    #
    @7
    wph
    @4
    @9
    wph
    @4
    wa
    #
    @9
    @2
    cF
    wwe
    @10
    vz
    cF
    va
    vb
    aomclem5.f
    wph
    @1
    con0
    wcel
    #
    @4
    aomclem5.on
    adantr
    wph
    @4
    simpr
    wph
    va
    cv
    #
    cr1
    cfv
    @12
    @0
    cfv
    wwe
    va
    @1
    wral
    #
    @4
    aomclem5.we
    adantr
    aomclem4
    @10
    @2
    @2
    @5
    cF
    @4
    @5
    cF
    wceq
    wph
    @4
    cF
    cE
    iftrue
    adantl
    @10
    @2
    eqidd
    weeq12d
    mpbird
    wph
    @4
    wn
    #
    wa
    #
    @9
    @2
    cE
    wwe
    @15
    vy
    vz
    cA
    cB
    cC
    cD
    cE
    va
    vb
    vc
    vd
    aomclem5.b
    aomclem5.c
    aomclem5.d
    aomclem5.e
    wph
    @11
    @14
    aomclem5.on
    adantr
    wph
    @4
    @1
    @3
    csuc
    wceq
    #
    wph
    @11
    @1
    word
    @4
    @16
    wo
    aomclem5.on
    @1
    eloni
    @1
    orduniorsuc
    3syl
    orcanai
    wph
    @13
    @14
    aomclem5.we
    adantr
    wph
    cA
    con0
    wcel
    @14
    aomclem5.a
    adantr
    wph
    @1
    cA
    wss
    @14
    aomclem5.za
    adantr
    wph
    @12
    c0
    wne
    @12
    vy
    cv
    cfv
    @12
    cpw
    cfn
    cin
    c0
    csn
    cdif
    wcel
    wi
    va
    cA
    cr1
    cfv
    cpw
    wral
    @14
    aomclem5.y
    adantr
    aomclem3
    @15
    @2
    @2
    @5
    cE
    @14
    @5
    cE
    wceq
    wph
    @4
    cF
    cE
    iffalse
    adantl
    @15
    @2
    eqidd
    weeq12d
    mpbird
    pm2.61dan
    @2
    @5
    weinxp
    sylib
    cG
    @6
    wceq
    @8
    @7
    wb
    aomclem5.g
    @2
    cG
    @6
    weeq1
    ax-mp
    sylibr
end
