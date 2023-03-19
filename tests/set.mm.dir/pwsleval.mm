include "wbr.mm"
include "cofr.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wceq.mm"
include "pwsle.mm"
include "syl2anc.mm"
include "breqd.mm"
include "wb.mm"
include "brinxp.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "eqid.mm"
include "pwselbas.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "wa.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "3bitr2d.mm"

theorem pwsleval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  assume pwsle.y: |- Y = ( R ^s I )
  assume pwsle.v: |- B = ( Base ` Y )
  assume pwsle.o: |- O = ( le ` R )
  assume pwsle.l: |- .<_ = ( le ` Y )
  assume pwsleval.r: |- ( ph -> R e. V )
  assume pwsleval.i: |- ( ph -> I e. W )
  assume pwsleval.a: |- ( ph -> F e. B )
  assume pwsleval.b: |- ( ph -> G e. B )

  disjoint B x
  disjoint I x
  disjoint O x
  disjoint R x
  disjoint V x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint W x
  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint I f
  disjoint I g
  disjoint O f
  disjoint O g
  disjoint R f
  disjoint R g
  disjoint V f
  disjoint V g
  disjoint W f
  disjoint W g
  assert |- ( ph -> ( F .<_ G <-> A. x e. I ( F ` x ) O ( G ` x ) ) )

  proof
    wph
    cF
    cG
    c.le
    wbr
    cF
    cG
    cO
    cofr
    #
    cB
    cB
    cxp
    cin
    #
    wbr
    #
    cF
    cG
    @0
    wbr
    #
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cO
    wbr
    vx
    cI
    wral
    wph
    c.le
    @1
    cF
    cG
    wph
    cR
    cV
    wcel
    cI
    cW
    wcel
    c.le
    @1
    wceq
    pwsleval.r
    pwsleval.i
    cB
    cR
    cI
    c.le
    cO
    cV
    cW
    cY
    pwsle.y
    pwsle.v
    pwsle.o
    pwsle.l
    pwsle
    syl2anc
    breqd
    wph
    cF
    cB
    wcel
    cG
    cB
    wcel
    @3
    @2
    wb
    pwsleval.a
    pwsleval.b
    cF
    cG
    cB
    cB
    @0
    brinxp
    syl2anc
    wph
    vx
    cI
    cI
    @5
    @6
    cO
    cI
    cF
    cG
    cW
    cW
    wph
    cI
    cR
    cbs
    cfv
    #
    cF
    wf
    cF
    cI
    wfn
    wph
    @7
    cR
    cI
    cB
    cV
    cF
    cY
    cW
    pwsle.y
    @7
    eqid
    #
    pwsle.v
    pwsleval.r
    pwsleval.i
    pwsleval.a
    pwselbas
    cI
    @7
    cF
    ffn
    syl
    wph
    cI
    @7
    cG
    wf
    cG
    cI
    wfn
    wph
    @7
    cR
    cI
    cB
    cV
    cG
    cY
    cW
    pwsle.y
    @8
    pwsle.v
    pwsleval.r
    pwsleval.i
    pwsleval.b
    pwselbas
    cI
    @7
    cG
    ffn
    syl
    pwsleval.i
    pwsleval.i
    cI
    inidm
    wph
    @4
    cI
    wcel
    wa
    #
    @5
    eqidd
    @9
    @6
    eqidd
    ofrfval
    3bitr2d
end
