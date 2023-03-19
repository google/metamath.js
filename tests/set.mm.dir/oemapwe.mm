include "wwe.mm"
include "coi.mm"
include "cdm.mm"
include "coe.mm"
include "co.mm"
include "wceq.mm"
include "cep.mm"
include "con0.mm"
include "wcel.mm"
include "word.mm"
include "oecl.mm"
include "syl2anc.mm"
include "eloni.mm"
include "ordwe.mm"
include "3syl.mm"
include "ccnf.mm"
include "wiso.mm"
include "wb.mm"
include "cantnf.mm"
include "isowe.mm"
include "syl.mm"
include "mpbird.mm"
include "ccnv.mm"
include "wa.mm"
include "isocnv.mm"
include "wse.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "eqeltri.mm"
include "exse.mm"
include "ax-mp.mm"
include "eqid.mm"
include "oieu.mm"
include "sylancl.mm"
include "mpbi2and.mm"
include "simpld.mm"
include "eqcomd.mm"
include "jca.mm"

theorem oemapwe
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h k
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b g
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint c d
  disjoint C c
  disjoint d g
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint C g
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D k
  disjoint D n
  disjoint D z
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint A c
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint A d
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T c
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint Y k
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X k
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c ph
  assert |- ( ph -> ( T We S /\ dom OrdIso ( T , S ) = ( A ^o B ) ) )

  proof
    wph
    cS
    cT
    wwe
    #
    cS
    cT
    coi
    #
    cdm
    #
    cA
    cB
    coe
    co
    #
    wceq
    wph
    @0
    @3
    cep
    wwe
    #
    wph
    @3
    con0
    wcel
    #
    @3
    word
    #
    @4
    wph
    cA
    con0
    wcel
    cB
    con0
    wcel
    @5
    cantnfs.a
    cantnfs.b
    cA
    cB
    oecl
    syl2anc
    #
    @3
    eloni
    #
    @3
    ordwe
    3syl
    wph
    cS
    @3
    cT
    cep
    cA
    cB
    ccnf
    co
    #
    wiso
    #
    @0
    @4
    wb
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    cT
    cantnfs.s
    cantnfs.a
    cantnfs.b
    oemapval.t
    cantnf
    #
    cS
    @3
    cT
    cep
    @9
    isowe
    syl
    mpbird
    #
    wph
    @3
    @2
    wph
    @3
    @2
    wceq
    #
    @9
    ccnv
    #
    @1
    wceq
    #
    wph
    @6
    @3
    cS
    cep
    cT
    @14
    wiso
    #
    @13
    @15
    wa
    #
    wph
    @5
    @6
    @7
    @8
    syl
    wph
    @10
    @16
    @11
    cS
    @3
    cT
    cep
    @9
    isocnv
    syl
    wph
    @0
    cS
    cT
    wse
    #
    @6
    @16
    wa
    @17
    wb
    @12
    cS
    cvv
    wcel
    @18
    cS
    @9
    cdm
    cvv
    cantnfs.s
    @9
    cA
    cB
    ccnf
    ovex
    dmex
    eqeltri
    cS
    cT
    cvv
    exse
    ax-mp
    cS
    @3
    cT
    @1
    @14
    @1
    eqid
    oieu
    sylancl
    mpbi2and
    simpld
    eqcomd
    jca
end
