include "cpw.mm"
include "wcel.mm"
include "clvec.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wne.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "clmod.mm"
include "csn.mm"
include "cdif.mm"
include "lveclmod.mm"
include "3anim2i.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "wa.mm"
include "wf.mm"
include "elmapi.mm"
include "simp3.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "simpr2.mm"
include "cdr.mm"
include "wb.mm"
include "lvecdrng.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "drngunit.mm"
include "syl.mm"
include "mpbir2and.mm"
include "3adant3.mm"
include "lincresunit3.mm"
include "syl131anc.mm"

theorem lincreslvec3
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint I s
  disjoint N s
  disjoint .x. s
  disjoint .0. s
  disjoint G s
  disjoint R s
  disjoint Z s
  disjoint s z
  disjoint B z
  disjoint E z
  disjoint F z
  disjoint G z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint S z
  disjoint U z
  disjoint X z
  disjoint Z z
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LVec /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) =/= .0. /\ F finSupp .0. ) /\ ( F ( linC ` M ) S ) = Z ) -> ( G ( linC ` M ) ( S \ { X } ) ) = X )

  proof
    cS
    cB
    cpw
    wcel
    #
    cM
    clvec
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cE
    cS
    cmap
    co
    wcel
    #
    cX
    cF
    cfv
    #
    c.0
    wne
    #
    cF
    c.0
    cfsupp
    wbr
    #
    w3a
    #
    cF
    cS
    cM
    clinc
    cfv
    #
    co
    cZ
    wceq
    #
    w3a
    @0
    cM
    clmod
    wcel
    #
    @2
    w3a
    #
    @4
    @5
    cU
    wcel
    #
    @7
    @10
    cG
    cS
    cX
    csn
    cdif
    @9
    co
    cX
    wceq
    @3
    @8
    @12
    @10
    @1
    @11
    @0
    @2
    cM
    lveclmod
    3anim2i
    3ad2ant1
    @3
    @4
    @6
    @7
    @10
    simp21
    @3
    @8
    @13
    @10
    @3
    @8
    wa
    #
    @13
    @5
    cE
    wcel
    #
    @6
    @8
    cS
    cE
    cF
    wf
    #
    @2
    @15
    @3
    @4
    @6
    @16
    @7
    cF
    cE
    cS
    elmapi
    3ad2ant1
    @0
    @1
    @2
    simp3
    cS
    cE
    cX
    cF
    ffvelrn
    syl2anr
    @3
    @4
    @6
    @7
    simpr2
    @14
    cR
    cdr
    wcel
    #
    @13
    @15
    @6
    wa
    wb
    @3
    @17
    @8
    @1
    @0
    @17
    @2
    cR
    cM
    lincresunit.r
    lvecdrng
    3ad2ant2
    adantr
    cE
    cR
    cU
    @5
    c.0
    lincresunit.e
    lincresunit.u
    lincresunit.0
    drngunit
    syl
    mpbir2and
    3adant3
    @8
    @3
    @7
    @10
    @4
    @6
    @7
    simp3
    3ad2ant2
    @3
    @8
    @10
    simp3
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit3
    syl131anc
end
