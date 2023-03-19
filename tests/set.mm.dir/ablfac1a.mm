include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "chash.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "fveq2d.mm"
include "cdiv.mm"
include "eqid.mm"
include "cabl.mm"
include "adantr.mm"
include "cn.mm"
include "cgcd.mm"
include "c1.mm"
include "cmul.mm"
include "ablfac1lem.mm"
include "simp1d.mm"
include "simpld.mm"
include "simprd.mm"
include "simp2d.mm"
include "simp3d.mm"
include "ablfacrp2.mm"
include "eqtrd.mm"

theorem ablfac1a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cO: class O
  let vp: setvar p
  let vq: setvar q
  let vw: setvar w
  let vy: setvar y
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cT: class T
  assume ablfac1.b: |- B = ( Base ` G )
  assume ablfac1.o: |- O = ( od ` G )
  assume ablfac1.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac1.g: |- ( ph -> G e. Abel )
  assume ablfac1.f: |- ( ph -> B e. Fin )
  assume ablfac1.1: |- ( ph -> A C_ Prime )

  disjoint p x
  disjoint B p
  disjoint B x
  disjoint p ph
  disjoint ph x
  disjoint A p
  disjoint A x
  disjoint O p
  disjoint O x
  disjoint P p
  disjoint P x
  disjoint G p
  disjoint G x
  disjoint p q
  disjoint p w
  disjoint p y
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint B q
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B y
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint q z
  disjoint ph q
  disjoint w z
  disjoint ph w
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint S q
  disjoint A a
  disjoint A b
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint O q
  disjoint O y
  disjoint P q
  disjoint P y
  disjoint P z
  disjoint T q
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint G a
  disjoint G b
  disjoint G q
  disjoint G y
  disjoint G z
  assert |- ( ( ph /\ P e. A ) -> ( # ` ( S ` P ) ) = ( P ^ ( P pCnt ( # ` B ) ) ) )

  proof
    wph
    cP
    cA
    wcel
    #
    wa
    #
    cP
    cS
    cfv
    #
    chash
    cfv
    vx
    cv
    cO
    cfv
    #
    cP
    cP
    cB
    chash
    cfv
    #
    cpc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    chash
    cfv
    #
    @6
    @1
    @2
    @8
    chash
    @0
    @2
    @8
    wceq
    wph
    vp
    cP
    @3
    vp
    cv
    #
    @10
    @4
    cpc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vx
    cB
    crab
    @8
    cA
    cS
    @10
    cP
    wceq
    #
    @13
    @7
    vx
    cB
    @14
    @12
    @6
    @3
    cdvds
    @14
    @10
    cP
    @11
    @5
    cexp
    @14
    id
    @10
    cP
    @4
    cpc
    oveq1
    oveq12d
    breq2d
    rabbidv
    ablfac1.s
    @13
    vx
    cB
    cB
    cG
    cbs
    cfv
    cvv
    ablfac1.b
    cG
    cbs
    fvex
    eqeltri
    rabex
    fvmpt3i
    adantl
    fveq2d
    @1
    @9
    @6
    wceq
    @3
    @4
    @6
    cdiv
    co
    #
    cdvds
    wbr
    vx
    cB
    crab
    #
    chash
    cfv
    @15
    wceq
    @1
    vx
    cB
    cG
    @8
    @16
    @6
    @15
    cO
    ablfac1.b
    ablfac1.o
    @8
    eqid
    @16
    eqid
    wph
    cG
    cabl
    wcel
    @0
    ablfac1.g
    adantr
    @1
    @6
    cn
    wcel
    #
    @15
    cn
    wcel
    #
    @1
    @17
    @18
    wa
    #
    @6
    @15
    cgcd
    co
    c1
    wceq
    #
    @4
    @6
    @15
    cmul
    co
    wceq
    #
    wph
    vx
    cA
    cB
    cP
    cS
    cG
    @6
    @15
    cO
    vp
    ablfac1.b
    ablfac1.o
    ablfac1.s
    ablfac1.g
    ablfac1.f
    ablfac1.1
    @6
    eqid
    @15
    eqid
    ablfac1lem
    #
    simp1d
    #
    simpld
    @1
    @17
    @18
    @23
    simprd
    @1
    @19
    @20
    @21
    @22
    simp2d
    @1
    @19
    @20
    @21
    @22
    simp3d
    ablfacrp2
    simpld
    eqtrd
end
