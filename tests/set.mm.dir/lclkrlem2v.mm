include "co.mm"
include "cfv.mm"
include "dvhlmod.mm"
include "ldualvaddcl.mm"
include "lkrssv.mm"
include "cpr.mm"
include "clss.mm"
include "eqid.mm"
include "lspprcl.mm"
include "cdih.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "dihprrn.mm"
include "wss.mm"
include "lssss.mm"
include "syl.mm"
include "dochoccl.mm"
include "mpbid.mm"
include "dochexmid.mm"
include "dvhlvec.mm"
include "lclkrlem2n.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "chlt.mm"
include "wa.mm"
include "snssd.mm"
include "dochdmj1.mm"
include "syl3anc.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "unssd.mm"
include "dochocsp.mm"
include "syl5eq.mm"
include "ineq12d.mm"
include "3eqtr4d.mm"
include "lkrin.mm"
include "eqsstrd.mm"
include "csubg.mm"
include "wb.mm"
include "clmod.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lkrlss.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem lclkrlem2v
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2m.v: |- V = ( Base ` U )
  assume lclkrlem2m.t: |- .x. = ( .s ` U )
  assume lclkrlem2m.s: |- S = ( Scalar ` U )
  assume lclkrlem2m.q: |- .X. = ( .r ` S )
  assume lclkrlem2m.z: |- .0. = ( 0g ` S )
  assume lclkrlem2m.i: |- I = ( invr ` S )
  assume lclkrlem2m.m: |- .- = ( -g ` U )
  assume lclkrlem2m.f: |- F = ( LFnl ` U )
  assume lclkrlem2m.d: |- D = ( LDual ` U )
  assume lclkrlem2m.p: |- .+ = ( +g ` D )
  assume lclkrlem2m.x: |- ( ph -> X e. V )
  assume lclkrlem2m.y: |- ( ph -> Y e. V )
  assume lclkrlem2m.e: |- ( ph -> E e. F )
  assume lclkrlem2m.g: |- ( ph -> G e. F )
  assume lclkrlem2n.n: |- N = ( LSpan ` U )
  assume lclkrlem2n.l: |- L = ( LKer ` U )
  assume lclkrlem2o.h: |- H = ( LHyp ` K )
  assume lclkrlem2o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2o.a: |- .(+) = ( LSSum ` U )
  assume lclkrlem2o.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2q.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2q.lg: |- ( ph -> ( L ` G ) = ( ._|_ ` { Y } ) )
  assume lclkrlem2v.j: |- ( ph -> ( ( E .+ G ) ` X ) = .0. )
  assume lclkrlem2v.k: |- ( ph -> ( ( E .+ G ) ` Y ) = .0. )


  assert |- ( ph -> ( L ` ( E .+ G ) ) = V )

  proof
    wph
    cE
    cG
    c.pl
    co
    #
    cL
    cfv
    #
    cV
    wph
    cF
    @0
    cL
    cV
    cU
    lclkrlem2m.v
    lclkrlem2m.f
    lclkrlem2n.l
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlmod
    #
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2m.f
    lclkrlem2m.d
    lclkrlem2m.p
    @2
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    lkrssv
    wph
    cV
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @5
    c.pe
    cfv
    #
    c.po
    co
    #
    @1
    wph
    c.po
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    c.pe
    cV
    cW
    @5
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2m.v
    @8
    eqid
    #
    lclkrlem2o.a
    lclkrlem2o.k
    wph
    @8
    cN
    cV
    cU
    cX
    cY
    lclkrlem2m.v
    @9
    lclkrlem2n.n
    @2
    lclkrlem2m.x
    lclkrlem2m.y
    lspprcl
    #
    wph
    @5
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    @6
    c.pe
    cfv
    @5
    wceq
    wph
    cU
    cH
    @11
    cK
    cN
    cV
    cW
    cX
    cY
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2n.n
    @11
    eqid
    #
    lclkrlem2o.k
    lclkrlem2m.x
    lclkrlem2m.y
    dihprrn
    wph
    cU
    cH
    @11
    cK
    c.pe
    cV
    cW
    @5
    lclkrlem2o.h
    @12
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2o.o
    lclkrlem2o.k
    wph
    @5
    @8
    wcel
    @5
    cV
    wss
    #
    @10
    @8
    @5
    cV
    cU
    lclkrlem2m.v
    @9
    lssss
    syl
    #
    dochoccl
    mpbid
    dochexmid
    wph
    @5
    @1
    wss
    #
    @6
    @1
    wss
    #
    @7
    @1
    wss
    #
    wph
    cD
    c.pl
    cS
    c.x
    c.xp
    cU
    cE
    cF
    cG
    cI
    cL
    c.mi
    cN
    cV
    cX
    cY
    c.0
    lclkrlem2m.v
    lclkrlem2m.t
    lclkrlem2m.s
    lclkrlem2m.q
    lclkrlem2m.z
    lclkrlem2m.i
    lclkrlem2m.m
    lclkrlem2m.f
    lclkrlem2m.d
    lclkrlem2m.p
    lclkrlem2m.x
    lclkrlem2m.y
    lclkrlem2m.e
    lclkrlem2m.g
    lclkrlem2n.n
    lclkrlem2n.l
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlvec
    lclkrlem2v.j
    lclkrlem2v.k
    lclkrlem2n
    wph
    @6
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
    @1
    wph
    cX
    csn
    #
    cY
    csn
    #
    cun
    #
    c.pe
    cfv
    #
    @21
    c.pe
    cfv
    #
    @22
    c.pe
    cfv
    #
    cin
    #
    @6
    @20
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @21
    cV
    wss
    @22
    cV
    wss
    @24
    @27
    wceq
    lclkrlem2o.k
    wph
    cX
    cV
    lclkrlem2m.x
    snssd
    #
    wph
    cY
    cV
    lclkrlem2m.y
    snssd
    #
    cU
    cH
    cK
    c.pe
    cV
    cW
    @21
    @22
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2o.o
    dochdmj1
    syl3anc
    wph
    @6
    @23
    cN
    cfv
    #
    c.pe
    cfv
    @24
    @5
    @31
    c.pe
    @4
    @23
    cN
    cX
    cY
    df-pr
    fveq2i
    fveq2i
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @23
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.o
    lclkrlem2m.v
    lclkrlem2n.n
    lclkrlem2o.k
    wph
    @21
    @22
    cV
    @29
    @30
    unssd
    dochocsp
    syl5eq
    wph
    @18
    @25
    @19
    @26
    lclkrlem2q.le
    lclkrlem2q.lg
    ineq12d
    3eqtr4d
    wph
    cD
    c.pl
    cF
    cE
    cG
    cL
    cU
    lclkrlem2m.f
    lclkrlem2n.l
    lclkrlem2m.d
    lclkrlem2m.p
    @2
    lclkrlem2m.e
    lclkrlem2m.g
    lkrin
    eqsstrd
    wph
    @5
    cU
    csubg
    cfv
    #
    wcel
    @6
    @32
    wcel
    @1
    @32
    wcel
    @15
    @16
    wa
    @17
    wb
    wph
    @8
    @32
    @5
    wph
    cU
    clmod
    wcel
    #
    @8
    @32
    wss
    @2
    @8
    cU
    @9
    lsssssubg
    syl
    #
    @10
    sseldd
    wph
    @8
    @32
    @6
    @34
    wph
    @28
    @13
    @6
    @8
    wcel
    lclkrlem2o.k
    @14
    @8
    cU
    cH
    cK
    c.pe
    cV
    cW
    @5
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2m.v
    @9
    lclkrlem2o.o
    dochlss
    syl2anc
    sseldd
    wph
    @8
    @32
    @1
    @34
    wph
    @33
    @0
    cF
    wcel
    @1
    @8
    wcel
    @2
    @3
    @8
    cF
    @0
    cL
    cU
    lclkrlem2m.f
    lclkrlem2n.l
    @9
    lkrlss
    syl2anc
    sseldd
    c.po
    @5
    @6
    @1
    cU
    lclkrlem2o.a
    lsmlub
    syl3anc
    mpbi2and
    eqsstr3d
    eqssd
end
