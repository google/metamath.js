include "cfv.mm"
include "cin.mm"
include "co.mm"
include "wss.mm"
include "csn.mm"
include "dvhlmod.mm"
include "lkrin.mm"
include "clss.mm"
include "eqid.mm"
include "lshplss.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "ldualvaddcl.mm"
include "eldifad.mm"
include "ellkr2.mm"
include "mpbird.mm"
include "lspsnel5a.mm"
include "csubg.mm"
include "wa.mm"
include "wb.mm"
include "lsssssubg.mm"
include "syl.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "lsmlub.mm"
include "mpbi2and.mm"

theorem lclkrlem2f
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2f.h: |- H = ( LHyp ` K )
  assume lclkrlem2f.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2f.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2f.v: |- V = ( Base ` U )
  assume lclkrlem2f.s: |- S = ( Scalar ` U )
  assume lclkrlem2f.q: |- Q = ( 0g ` S )
  assume lclkrlem2f.z: |- .0. = ( 0g ` U )
  assume lclkrlem2f.a: |- .(+) = ( LSSum ` U )
  assume lclkrlem2f.n: |- N = ( LSpan ` U )
  assume lclkrlem2f.f: |- F = ( LFnl ` U )
  assume lclkrlem2f.j: |- J = ( LSHyp ` U )
  assume lclkrlem2f.l: |- L = ( LKer ` U )
  assume lclkrlem2f.d: |- D = ( LDual ` U )
  assume lclkrlem2f.p: |- .+ = ( +g ` D )
  assume lclkrlem2f.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2f.b: |- ( ph -> B e. ( V \ { .0. } ) )
  assume lclkrlem2f.e: |- ( ph -> E e. F )
  assume lclkrlem2f.g: |- ( ph -> G e. F )
  assume lclkrlem2f.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2f.lg: |- ( ph -> ( L ` G ) = ( ._|_ ` { Y } ) )
  assume lclkrlem2f.kb: |- ( ph -> ( ( E .+ G ) ` B ) = Q )
  assume lclkrlem2f.nx: |- ( ph -> ( -. X e. ( ._|_ ` { B } ) \/ -. Y e. ( ._|_ ` { B } ) ) )
  assume lclkrlem2f.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2f.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lclkrlem2f.ne: |- ( ph -> ( L ` E ) =/= ( L ` G ) )
  assume lclkrlem2f.lp: |- ( ph -> ( L ` ( E .+ G ) ) e. J )


  assert |- ( ph -> ( ( ( L ` E ) i^i ( L ` G ) ) .(+) ( N ` { B } ) ) C_ ( L ` ( E .+ G ) ) )

  proof
    wph
    cE
    cL
    cfv
    #
    cG
    cL
    cfv
    #
    cin
    #
    cE
    cG
    c.pl
    co
    #
    cL
    cfv
    #
    wss
    #
    cB
    csn
    cN
    cfv
    #
    @4
    wss
    #
    @2
    @6
    c.po
    co
    @4
    wss
    #
    wph
    cD
    c.pl
    cF
    cE
    cG
    cL
    cU
    lclkrlem2f.f
    lclkrlem2f.l
    lclkrlem2f.d
    lclkrlem2f.p
    wph
    cU
    cH
    cK
    cW
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.k
    dvhlmod
    #
    lclkrlem2f.e
    lclkrlem2f.g
    lkrin
    wph
    cU
    clss
    cfv
    #
    @4
    cN
    cU
    cB
    @10
    eqid
    #
    lclkrlem2f.n
    @9
    wph
    @10
    @4
    cJ
    cU
    @11
    lclkrlem2f.j
    @9
    lclkrlem2f.lp
    lshplss
    #
    wph
    cB
    @4
    wcel
    cB
    @3
    cfv
    cQ
    wceq
    lclkrlem2f.kb
    wph
    cS
    cF
    @3
    cL
    cV
    cU
    cB
    clmod
    cQ
    lclkrlem2f.v
    lclkrlem2f.s
    lclkrlem2f.q
    lclkrlem2f.f
    lclkrlem2f.l
    @9
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2f.f
    lclkrlem2f.d
    lclkrlem2f.p
    @9
    lclkrlem2f.e
    lclkrlem2f.g
    ldualvaddcl
    wph
    cB
    cV
    c.0
    csn
    lclkrlem2f.b
    eldifad
    #
    ellkr2
    mpbird
    lspsnel5a
    wph
    @2
    cU
    csubg
    cfv
    #
    wcel
    @6
    @14
    wcel
    @4
    @14
    wcel
    @5
    @7
    wa
    @8
    wb
    wph
    @10
    @14
    @2
    wph
    cU
    clmod
    wcel
    #
    @10
    @14
    wss
    @9
    @10
    cU
    @11
    lsssssubg
    syl
    #
    wph
    @15
    @0
    @10
    wcel
    #
    @1
    @10
    wcel
    #
    @2
    @10
    wcel
    @9
    wph
    @15
    cE
    cF
    wcel
    @17
    @9
    lclkrlem2f.e
    @10
    cF
    cE
    cL
    cU
    lclkrlem2f.f
    lclkrlem2f.l
    @11
    lkrlss
    syl2anc
    wph
    @15
    cG
    cF
    wcel
    @18
    @9
    lclkrlem2f.g
    @10
    cF
    cG
    cL
    cU
    lclkrlem2f.f
    lclkrlem2f.l
    @11
    lkrlss
    syl2anc
    @10
    @0
    @1
    cU
    @11
    lssincl
    syl3anc
    sseldd
    wph
    @10
    @14
    @6
    @16
    wph
    @15
    cB
    cV
    wcel
    @6
    @10
    wcel
    @9
    @13
    @10
    cN
    cV
    cU
    cB
    lclkrlem2f.v
    @11
    lclkrlem2f.n
    lspsncl
    syl2anc
    sseldd
    wph
    @10
    @14
    @4
    @16
    @12
    sseldd
    c.po
    @2
    @6
    @4
    cU
    lclkrlem2f.a
    lsmlub
    syl3anc
    mpbi2and
end
