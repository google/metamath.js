include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "wcel.mm"
include "eqid.mm"
include "matbas2i.mm"
include "syl.mm"
include "smatrcl.mm"
include "cfn.mm"
include "cvv.mm"
include "wceq.mm"
include "fzfi.mm"
include "matrcl.mm"
include "simprd.mm"
include "matbas2.mm"
include "sylancr.mm"
include "eleq2d.mm"
include "mpbid.mm"
include "syl6eleqr.mm"

theorem smatcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume smatcl.a: |- A = ( ( 1 ... N ) Mat R )
  assume smatcl.b: |- B = ( Base ` A )
  assume smatcl.c: |- C = ( Base ` ( ( 1 ... ( N - 1 ) ) Mat R ) )
  assume smatcl.s: |- S = ( K ( subMat1 ` M ) L )
  assume smatcl.n: |- ( ph -> N e. NN )
  assume smatcl.k: |- ( ph -> K e. ( 1 ... N ) )
  assume smatcl.l: |- ( ph -> L e. ( 1 ... N ) )
  assume smatcl.m: |- ( ph -> M e. B )


  assert |- ( ph -> S e. C )

  proof
    wph
    cS
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cC
    wph
    cS
    cR
    cbs
    cfv
    #
    @1
    @1
    cxp
    cmap
    co
    #
    wcel
    cS
    @3
    wcel
    wph
    cM
    @4
    cS
    cK
    cL
    cN
    cN
    smatcl.s
    smatcl.n
    smatcl.n
    smatcl.k
    smatcl.l
    wph
    cM
    cB
    wcel
    #
    cM
    @4
    c1
    cN
    cfz
    co
    #
    @7
    cxp
    cmap
    co
    wcel
    smatcl.m
    cA
    cB
    cR
    @4
    cM
    @7
    smatcl.a
    @4
    eqid
    #
    smatcl.b
    matbas2i
    syl
    smatrcl
    wph
    @5
    @3
    cS
    wph
    @1
    cfn
    wcel
    cR
    cvv
    wcel
    #
    @5
    @3
    wceq
    c1
    @0
    fzfi
    wph
    @6
    @9
    smatcl.m
    @6
    @7
    cfn
    wcel
    @9
    cA
    cB
    cR
    @7
    cM
    smatcl.a
    smatcl.b
    matrcl
    simprd
    syl
    @2
    cR
    @4
    @1
    cvv
    @2
    eqid
    @8
    matbas2
    sylancr
    eleq2d
    mpbid
    smatcl.c
    syl6eleqr
end
