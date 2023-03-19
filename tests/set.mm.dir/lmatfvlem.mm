include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "cfz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "caddc.mm"
include "cn0.mm"
include "nn0p1nn.mm"
include "ax-mp.mm"
include "eqeltrri.mm"
include "nnge1.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "1z.mm"
include "nnzd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "lmatfval.mm"
include "wceq.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "pncan3oi.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "fveq2i.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"

theorem lmatfvlem
  let wph: wff ph
  let vi: setvar i
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vm: setvar m
  assume lmatfval.m: |- M = ( litMat ` W )
  assume lmatfval.n: |- ( ph -> N e. NN )
  assume lmatfval.w: |- ( ph -> W e. Word Word V )
  assume lmatfval.1: |- ( ph -> ( # ` W ) = N )
  assume lmatfval.2: |- ( ( ph /\ i e. ( 0 ..^ N ) ) -> ( # ` ( W ` i ) ) = N )
  assume lmatfvlem.1: |- K e. NN0
  assume lmatfvlem.2: |- L e. NN0
  assume lmatfvlem.3: |- I <_ N
  assume lmatfvlem.4: |- J <_ N
  assume lmatfvlem.5: |- ( K + 1 ) = I
  assume lmatfvlem.6: |- ( L + 1 ) = J
  assume lmatfvlem.7: |- ( W ` K ) = X
  assume lmatfvlem.8: |- ( ph -> ( X ` L ) = Y )

  disjoint M i
  disjoint I i
  disjoint J i
  disjoint N i
  disjoint W i
  disjoint i ph
  disjoint M j
  disjoint M m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint I j
  disjoint J j
  disjoint W j
  disjoint j ph
  assert |- ( ph -> ( I M J ) = Y )

  proof
    wph
    cI
    cJ
    cM
    co
    cJ
    c1
    cmin
    co
    #
    cI
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cfv
    @0
    cX
    cfv
    #
    cY
    wph
    vi
    cI
    cJ
    cM
    cN
    cV
    cW
    lmatfval.m
    lmatfval.n
    lmatfval.w
    lmatfval.1
    lmatfval.2
    wph
    cI
    c1
    cN
    cfz
    co
    #
    wcel
    #
    c1
    cI
    cle
    wbr
    #
    cI
    cN
    cle
    wbr
    #
    wa
    #
    @8
    wph
    @6
    @7
    cI
    cn
    wcel
    #
    @6
    cK
    c1
    caddc
    co
    #
    cI
    cn
    lmatfvlem.5
    cK
    cn0
    wcel
    @10
    cn
    wcel
    lmatfvlem.1
    cK
    nn0p1nn
    ax-mp
    eqeltrri
    #
    cI
    nnge1
    ax-mp
    lmatfvlem.3
    pm3.2i
    a1i
    wph
    cI
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @5
    @8
    wb
    @12
    wph
    @9
    @12
    @11
    cI
    nnz
    ax-mp
    a1i
    @13
    wph
    1z
    a1i
    #
    wph
    cN
    lmatfval.n
    nnzd
    #
    cI
    c1
    cN
    elfz
    syl3anc
    mpbird
    wph
    cJ
    @4
    wcel
    #
    c1
    cJ
    cle
    wbr
    #
    cJ
    cN
    cle
    wbr
    #
    wa
    #
    @20
    wph
    @18
    @19
    cJ
    cn
    wcel
    #
    @18
    cL
    c1
    caddc
    co
    #
    cJ
    cn
    lmatfvlem.6
    cL
    cn0
    wcel
    @22
    cn
    wcel
    lmatfvlem.2
    cL
    nn0p1nn
    ax-mp
    eqeltrri
    #
    cJ
    nnge1
    ax-mp
    lmatfvlem.4
    pm3.2i
    a1i
    wph
    cJ
    cz
    wcel
    #
    @13
    @14
    @17
    @20
    wb
    @24
    wph
    @21
    @24
    @23
    cJ
    nnz
    ax-mp
    a1i
    @15
    @16
    cJ
    c1
    cN
    elfz
    syl3anc
    mpbird
    lmatfval
    wph
    @0
    @2
    cX
    @2
    cX
    wceq
    wph
    cK
    cW
    cfv
    @2
    cX
    cK
    @1
    cW
    @10
    c1
    cmin
    co
    cK
    @1
    cK
    c1
    cK
    lmatfvlem.1
    nn0cni
    ax-1cn
    pncan3oi
    @10
    cI
    c1
    cmin
    lmatfvlem.5
    oveq1i
    eqtr3i
    fveq2i
    lmatfvlem.7
    eqtr3i
    a1i
    fveq1d
    wph
    cL
    cX
    cfv
    @3
    cY
    wph
    cL
    @0
    cX
    cL
    @0
    wceq
    wph
    @22
    c1
    cmin
    co
    cL
    @0
    cL
    c1
    cL
    lmatfvlem.2
    nn0cni
    ax-1cn
    pncan3oi
    @22
    cJ
    c1
    cmin
    lmatfvlem.6
    oveq1i
    eqtr3i
    a1i
    fveq2d
    lmatfvlem.8
    eqtr3d
    3eqtrd
end
