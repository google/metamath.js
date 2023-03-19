include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "simp2.mm"
include "wss.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "sseldd.mm"
include "eqid.mm"
include "mulgnn.mm"
include "syl2anc.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cv.mm"
include "cfz.mm"
include "wa.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "simpl3.mm"
include "eqeltrd.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "seqcl.mm"

theorem mulgnnsubcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cI: class I
  assume mulgnnsubcl.b: |- B = ( Base ` G )
  assume mulgnnsubcl.t: |- .x. = ( .g ` G )
  assume mulgnnsubcl.p: |- .+ = ( +g ` G )
  assume mulgnnsubcl.g: |- ( ph -> G e. V )
  assume mulgnnsubcl.s: |- ( ph -> S C_ B )
  assume mulgnnsubcl.c: |- ( ( ph /\ x e. S /\ y e. S ) -> ( x .+ y ) e. S )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint .x. x
  disjoint X x
  disjoint X y
  disjoint I x
  assert |- ( ( ph /\ N e. NN /\ X e. S ) -> ( N .x. X ) e. S )

  proof
    wph
    cN
    cn
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cN
    cX
    c.x
    co
    #
    cN
    c.pl
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cS
    @2
    @0
    cX
    cB
    wcel
    @3
    @6
    wceq
    wph
    @0
    @1
    simp2
    #
    @2
    cS
    cB
    cX
    wph
    @0
    cS
    cB
    wss
    @1
    mulgnnsubcl.s
    3ad2ant1
    wph
    @0
    @1
    simp3
    #
    sseldd
    cB
    c.pl
    @5
    c.x
    cG
    cN
    cX
    mulgnnsubcl.b
    mulgnnsubcl.p
    mulgnnsubcl.t
    @5
    eqid
    mulgnn
    syl2anc
    @2
    vx
    vy
    c.pl
    cS
    @4
    c1
    cN
    @2
    cN
    cn
    c1
    cuz
    cfv
    @7
    nnuz
    syl6eleq
    @2
    vx
    cv
    #
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    @9
    @4
    cfv
    #
    cX
    cS
    @2
    @1
    @9
    cn
    wcel
    @11
    cX
    wceq
    @10
    @8
    @9
    cN
    elfznn
    cn
    cX
    @9
    cS
    fvconst2g
    syl2an
    wph
    @0
    @1
    @10
    simpl3
    eqeltrd
    wph
    @0
    @9
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @9
    @13
    c.pl
    co
    cS
    wcel
    #
    @1
    wph
    @12
    @14
    @15
    mulgnnsubcl.c
    3expb
    3ad2antl1
    seqcl
    eqeltrd
end
