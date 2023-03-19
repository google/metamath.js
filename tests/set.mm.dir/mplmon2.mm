include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cfv.mm"
include "cof.mm"
include "cbs.mm"
include "eqid.mm"
include "mplmon.mm"
include "mplvsca.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "adantr.mm"
include "wa.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "crg.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "wn.mm"
include "ringrz.mm"
include "iffalse.mm"
include "ifbothda.mm"
include "mpteq2dv.mm"
include "3eqtrd.mm"

theorem mplmon2
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume mplmon2.p: |- P = ( I mPoly R )
  assume mplmon2.v: |- .x. = ( .s ` P )
  assume mplmon2.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplmon2.o: |- .1. = ( 1r ` R )
  assume mplmon2.z: |- .0. = ( 0g ` R )
  assume mplmon2.b: |- B = ( Base ` R )
  assume mplmon2.i: |- ( ph -> I e. W )
  assume mplmon2.r: |- ( ph -> R e. Ring )
  assume mplmon2.k: |- ( ph -> K e. D )
  assume mplmon2.x: |- ( ph -> X e. B )

  disjoint ph y
  disjoint B y
  disjoint D y
  disjoint I f
  disjoint K f
  disjoint K y
  disjoint f y
  disjoint .1. y
  disjoint R y
  disjoint X y
  disjoint .0. y
  assert |- ( ph -> ( X .x. ( y e. D |-> if ( y = K , .1. , .0. ) ) ) = ( y e. D |-> if ( y = K , X , .0. ) ) )

  proof
    wph
    cX
    vy
    cD
    vy
    cv
    #
    cK
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    c.x
    co
    cD
    cX
    csn
    cxp
    #
    @3
    cR
    cmulr
    cfv
    #
    cof
    co
    vy
    cD
    cX
    @2
    @5
    co
    #
    cmpt
    vy
    cD
    @1
    cX
    c.0
    cif
    #
    cmpt
    wph
    cP
    cbs
    cfv
    #
    cD
    cP
    cR
    c.x
    @5
    vf
    @3
    cI
    cB
    cX
    mplmon2.p
    mplmon2.v
    mplmon2.b
    @8
    eqid
    #
    @5
    eqid
    #
    mplmon2.d
    mplmon2.x
    wph
    vy
    @8
    cD
    cP
    cR
    c.1
    vf
    cI
    cW
    cK
    c.0
    mplmon2.p
    @9
    mplmon2.z
    mplmon2.o
    mplmon2.d
    mplmon2.i
    mplmon2.r
    mplmon2.k
    mplmon
    mplvsca
    wph
    vy
    cD
    cX
    @2
    @5
    @4
    @3
    cvv
    cB
    cvv
    cD
    cvv
    wcel
    wph
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    mplmon2.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    wph
    cX
    cB
    wcel
    #
    @0
    cD
    wcel
    #
    mplmon2.x
    adantr
    @2
    cvv
    wcel
    wph
    @12
    wa
    @1
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    mplmon2.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    mplmon2.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    a1i
    @4
    vy
    cD
    cX
    cmpt
    wceq
    wph
    vy
    cD
    cX
    fconstmpt
    a1i
    wph
    @3
    eqidd
    offval2
    wph
    vy
    cD
    @6
    @7
    @1
    cX
    c.1
    @5
    co
    #
    @7
    wceq
    cX
    c.0
    @5
    co
    #
    @7
    wceq
    @6
    @7
    wceq
    wph
    c.1
    c.0
    c.1
    @2
    wceq
    @13
    @6
    @7
    c.1
    @2
    cX
    @5
    oveq2
    eqeq1d
    c.0
    @2
    wceq
    @14
    @6
    @7
    c.0
    @2
    cX
    @5
    oveq2
    eqeq1d
    wph
    @1
    @13
    cX
    @7
    wph
    cR
    crg
    wcel
    #
    @11
    @13
    cX
    wceq
    mplmon2.r
    mplmon2.x
    cB
    cR
    @5
    c.1
    cX
    mplmon2.b
    @10
    mplmon2.o
    ringridm
    syl2anc
    @1
    @7
    cX
    @1
    cX
    c.0
    iftrue
    eqcomd
    sylan9eq
    wph
    @1
    wn
    #
    @14
    c.0
    @7
    wph
    @15
    @11
    @14
    c.0
    wceq
    mplmon2.r
    mplmon2.x
    cB
    cR
    @5
    cX
    c.0
    mplmon2.b
    @10
    mplmon2.z
    ringrz
    syl2anc
    @16
    @7
    c.0
    @1
    cX
    c.0
    iffalse
    eqcomd
    sylan9eq
    ifbothda
    mpteq2dv
    3eqtrd
end
