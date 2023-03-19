include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "cn0.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl1.mm"
include "simpl2.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantl.mm"
include "mat2pmatbas.mm"
include "syl3anc.mm"

theorem m2pmfzmap
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cY: class Y
  let vb: setvar b
  assume m2pmfzmap.a: |- A = ( N Mat R )
  assume m2pmfzmap.b: |- B = ( Base ` A )
  assume m2pmfzmap.p: |- P = ( Poly1 ` R )
  assume m2pmfzmap.y: |- Y = ( N Mat P )
  assume m2pmfzmap.t: |- T = ( N matToPolyMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ S e. NN0 ) /\ ( b e. ( B ^m ( 0 ... S ) ) /\ I e. ( 0 ... S ) ) ) -> ( T ` ( b ` I ) ) e. ( Base ` Y ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cS
    cn0
    wcel
    #
    w3a
    #
    vb
    cv
    #
    cB
    cc0
    cS
    cfz
    co
    #
    cmap
    co
    wcel
    #
    cI
    @5
    wcel
    wa
    #
    wa
    @0
    @1
    cI
    @4
    cfv
    #
    cB
    wcel
    #
    @8
    cT
    cfv
    cY
    cbs
    cfv
    wcel
    @0
    @1
    @2
    @7
    simpl1
    @0
    @1
    @2
    @7
    simpl2
    @7
    @9
    @3
    @6
    @5
    cB
    cI
    @4
    @4
    cB
    @5
    elmapi
    ffvelrnda
    adantl
    cA
    cB
    cY
    cP
    cR
    cT
    @8
    cN
    m2pmfzmap.t
    m2pmfzmap.a
    m2pmfzmap.b
    m2pmfzmap.p
    m2pmfzmap.y
    mat2pmatbas
    syl3anc
end
