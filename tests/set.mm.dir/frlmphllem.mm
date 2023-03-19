include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "cfn.mm"
include "cof.mm"
include "wf.mm"
include "wfn.mm"
include "cmap.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "frlmbasmap.mm"
include "syl2anc.mm"
include "elmapi.mm"
include "syl.mm"
include "ffn.mm"
include "simp3.mm"
include "inidm.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "oveq1d.mm"
include "cvv.mm"
include "wfun.mm"
include "wss.mm"
include "ovexd.mm"
include "wceq.mm"
include "funmpt.mm"
include "a1i.mm"
include "funeq.mm"
include "mpbird.mm"
include "frlmbasfsupp.mm"
include "crg.mm"
include "cdr.mm"
include "ccrg.mm"
include "cfield.mm"
include "isfld.mm"
include "sylib.mm"
include "simpld.mm"
include "drngring.mm"
include "ring0cl.mm"
include "ringlz.mm"
include "sylan.mm"
include "suppofss1d.mm"
include "fsuppsssupp.mm"
include "fsuppimpd.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "mptexg.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "funisfsupp.mm"
include "syl3anc.mm"

theorem frlmphllem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let vg: setvar g
  let vh: setvar h
  let c.xi: class .,
  let cI: class I
  let c.as: class .*
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cX: class X
  let ve: setvar e
  let vi: setvar i
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume frlmphl.y: |- Y = ( R freeLMod I )
  assume frlmphl.b: |- B = ( Base ` R )
  assume frlmphl.t: |- .x. = ( .r ` R )
  assume frlmphl.v: |- V = ( Base ` Y )
  assume frlmphl.j: |- ., = ( .i ` Y )
  assume frlmphl.o: |- O = ( 0g ` Y )
  assume frlmphl.0: |- .0. = ( 0g ` R )
  assume frlmphl.s: |- .* = ( *r ` R )
  assume frlmphl.f: |- ( ph -> R e. Field )
  assume frlmphl.m: |- ( ( ph /\ g e. V /\ ( g ., g ) = .0. ) -> g = O )
  assume frlmphl.u: |- ( ( ph /\ x e. B ) -> ( .* ` x ) = x )
  assume frlmphl.i: |- ( ph -> I e. W )

  disjoint B g
  disjoint B x
  disjoint g x
  disjoint I g
  disjoint I x
  disjoint R g
  disjoint R x
  disjoint V g
  disjoint V x
  disjoint W g
  disjoint W x
  disjoint .x. g
  disjoint .x. x
  disjoint B h
  disjoint g h
  disjoint h x
  disjoint I h
  disjoint R h
  disjoint V h
  disjoint W h
  disjoint Y g
  disjoint Y h
  disjoint Y x
  disjoint .0. g
  disjoint .0. h
  disjoint .0. x
  disjoint g ph
  disjoint h ph
  disjoint ph x
  disjoint ., g
  disjoint ., h
  disjoint ., x
  disjoint .x. h
  disjoint O g
  disjoint O h
  disjoint .* x
  disjoint B f
  disjoint f g
  disjoint f x
  disjoint I f
  disjoint R f
  disjoint V f
  disjoint W f
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint .x. f
  disjoint B e
  disjoint B i
  disjoint B y
  disjoint B z
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f h
  disjoint f i
  disjoint f y
  disjoint f z
  disjoint g i
  disjoint g y
  disjoint g z
  disjoint h i
  disjoint h y
  disjoint h z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I e
  disjoint I i
  disjoint I y
  disjoint I z
  disjoint R e
  disjoint R i
  disjoint V e
  disjoint V i
  disjoint V y
  disjoint V z
  disjoint W i
  disjoint Y e
  disjoint Y f
  disjoint Y i
  disjoint Y k
  disjoint e k
  disjoint f k
  disjoint g k
  disjoint h k
  disjoint i k
  disjoint k x
  disjoint .0. f
  disjoint .0. i
  disjoint .0. y
  disjoint e ph
  disjoint f ph
  disjoint i ph
  disjoint k y
  disjoint k z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint ., i
  disjoint .x. e
  disjoint .x. i
  disjoint .x. y
  disjoint .x. z
  disjoint O i
  assert |- ( ( ph /\ g e. V /\ h e. V ) -> ( x e. I |-> ( ( g ` x ) .x. ( h ` x ) ) ) finSupp .0. )

  proof
    wph
    vg
    cv
    #
    cV
    wcel
    #
    vh
    cv
    #
    cV
    wcel
    #
    w3a
    #
    vx
    cI
    vx
    cv
    #
    @0
    cfv
    #
    @5
    @2
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    c.0
    cfsupp
    wbr
    #
    @9
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @4
    @0
    @2
    c.x
    cof
    #
    co
    #
    c.0
    csupp
    co
    #
    @11
    cfn
    @4
    @14
    @9
    c.0
    csupp
    @4
    vx
    cI
    cI
    @6
    @7
    c.x
    cI
    @0
    @2
    cW
    cW
    @4
    cI
    cB
    @0
    wf
    #
    @0
    cI
    wfn
    @4
    @0
    cB
    cI
    cmap
    co
    #
    wcel
    #
    @16
    @4
    cI
    cW
    wcel
    #
    @1
    @18
    wph
    @1
    @19
    @3
    frlmphl.i
    3ad2ant1
    #
    wph
    @1
    @3
    simp2
    #
    cV
    cR
    cY
    cI
    cB
    cW
    @0
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    syl2anc
    @0
    cB
    cI
    elmapi
    syl
    #
    cI
    cB
    @0
    ffn
    syl
    @4
    cI
    cB
    @2
    wf
    #
    @2
    cI
    wfn
    @4
    @2
    @17
    wcel
    #
    @23
    @4
    @19
    @3
    @24
    @20
    wph
    @1
    @3
    simp3
    cV
    cR
    cY
    cI
    cB
    cW
    @2
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    syl2anc
    @2
    cB
    cI
    elmapi
    syl
    #
    cI
    cB
    @2
    ffn
    syl
    @20
    @20
    cI
    inidm
    @4
    @5
    cI
    wcel
    wa
    #
    @6
    eqidd
    @26
    @7
    eqidd
    offval
    #
    oveq1d
    @4
    @14
    cvv
    wcel
    #
    @14
    wfun
    #
    @0
    c.0
    cfsupp
    wbr
    #
    @15
    @0
    c.0
    csupp
    co
    wss
    #
    @15
    cfn
    wcel
    @4
    @0
    @2
    @13
    ovexd
    @4
    @14
    @9
    wceq
    #
    @29
    @27
    @32
    @29
    @9
    wfun
    #
    @33
    @32
    vx
    cI
    @8
    funmpt
    #
    a1i
    @14
    @9
    funeq
    mpbird
    syl
    @4
    @19
    @1
    @30
    @20
    @21
    cV
    cR
    cY
    cI
    cW
    @0
    c.0
    frlmphl.y
    frlmphl.0
    frlmphl.v
    frlmbasfsupp
    syl2anc
    @4
    vx
    cI
    cB
    @0
    @2
    cW
    c.x
    c.0
    @20
    @4
    cR
    crg
    wcel
    #
    c.0
    cB
    wcel
    wph
    @1
    @35
    @3
    wph
    cR
    cdr
    wcel
    #
    @35
    wph
    @36
    cR
    ccrg
    wcel
    #
    wph
    cR
    cfield
    wcel
    @36
    @37
    wa
    frlmphl.f
    cR
    isfld
    sylib
    simpld
    cR
    drngring
    syl
    3ad2ant1
    #
    cB
    cR
    c.0
    frlmphl.b
    frlmphl.0
    ring0cl
    syl
    @22
    @25
    @4
    @35
    @5
    cB
    wcel
    c.0
    @5
    c.x
    co
    c.0
    wceq
    @38
    cB
    cR
    c.x
    @5
    c.0
    frlmphl.b
    frlmphl.t
    frlmphl.0
    ringlz
    sylan
    suppofss1d
    @28
    @29
    wa
    @30
    @31
    wa
    wa
    @14
    c.0
    @0
    @14
    cvv
    c.0
    fsuppsssupp
    fsuppimpd
    syl22anc
    eqeltrrd
    @4
    @33
    @9
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @10
    @12
    wb
    @33
    @4
    @34
    a1i
    @4
    @19
    @39
    @20
    vx
    cI
    @8
    cW
    mptexg
    syl
    @40
    @4
    c.0
    cR
    c0g
    cfv
    cvv
    frlmphl.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    @9
    cvv
    cvv
    c.0
    funisfsupp
    syl3anc
    mpbird
end
