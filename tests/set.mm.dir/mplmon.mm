include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "wf.mm"
include "crg.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "syl.mm"
include "adantr.mm"
include "fmptd.mm"
include "fvex.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "ovex.mm"
include "rabex2.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrbas.mm"
include "eleqtrrd.mm"
include "cvv.mm"
include "wfun.mm"
include "w3a.mm"
include "csn.mm"
include "csupp.mm"
include "wss.mm"
include "mptex.mm"
include "funmpt.mm"
include "c0g.mm"
include "eqeltri.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "snfi.mm"
include "cdif.mm"
include "wa.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "mplelbas.mm"
include "sylanbrc.mm"

theorem mplmon
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  let cY: class Y
  assume mplmon.s: |- P = ( I mPoly R )
  assume mplmon.b: |- B = ( Base ` P )
  assume mplmon.z: |- .0. = ( 0g ` R )
  assume mplmon.o: |- .1. = ( 1r ` R )
  assume mplmon.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplmon.i: |- ( ph -> I e. W )
  assume mplmon.r: |- ( ph -> R e. Ring )
  assume mplmon.x: |- ( ph -> X e. D )

  disjoint D y
  disjoint I f
  disjoint ph y
  disjoint f y
  disjoint X f
  disjoint X y
  disjoint .0. y
  disjoint .1. y
  disjoint R y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D z
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f z
  disjoint I j
  disjoint I k
  disjoint I x
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X z
  disjoint .0. j
  disjoint .0. k
  disjoint .1. j
  disjoint .1. k
  disjoint R j
  disjoint R k
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint W x
  assert |- ( ph -> ( y e. D |-> if ( y = X , .1. , .0. ) ) e. B )

  proof
    wph
    vy
    cD
    vy
    cv
    #
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    wcel
    @3
    c.0
    cfsupp
    wbr
    #
    @3
    cB
    wcel
    wph
    @3
    cR
    cbs
    cfv
    #
    cD
    cmap
    co
    #
    @5
    wph
    cD
    @7
    @3
    wf
    @3
    @8
    wcel
    wph
    vy
    cD
    @2
    @7
    @3
    wph
    @2
    @7
    wcel
    #
    @0
    cD
    wcel
    wph
    cR
    crg
    wcel
    #
    @9
    mplmon.r
    @10
    @1
    c.1
    c.0
    @7
    @7
    cR
    c.1
    @7
    eqid
    #
    mplmon.o
    ringidcl
    @7
    cR
    c.0
    @11
    mplmon.z
    ring0cl
    ifcld
    syl
    adantr
    @3
    eqid
    fmptd
    @7
    cD
    @3
    cR
    cbs
    fvex
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
    mplmon.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    elmap
    sylibr
    wph
    @5
    cD
    cR
    @4
    vf
    cI
    @7
    cW
    @4
    eqid
    #
    @11
    mplmon.d
    @5
    eqid
    #
    mplmon.i
    psrbas
    eleqtrrd
    wph
    @3
    cvv
    wcel
    #
    @3
    wfun
    #
    c.0
    cvv
    wcel
    #
    w3a
    #
    cX
    csn
    #
    cfn
    wcel
    #
    @3
    c.0
    csupp
    co
    @19
    wss
    @6
    @18
    wph
    @15
    @16
    @17
    vy
    cD
    @2
    @12
    mptex
    vy
    cD
    @2
    funmpt
    c.0
    cR
    c0g
    cfv
    cvv
    mplmon.z
    cR
    c0g
    fvex
    eqeltri
    3pm3.2i
    a1i
    @20
    wph
    cX
    snfi
    a1i
    wph
    cD
    @2
    vy
    cvv
    @19
    c.0
    wph
    @0
    cD
    @19
    cdif
    wcel
    #
    wa
    #
    @1
    c.1
    c.0
    @22
    @0
    cX
    @21
    @0
    cX
    wne
    wph
    @0
    cD
    cX
    eldifsni
    adantl
    neneqd
    iffalsed
    cD
    cvv
    wcel
    wph
    @12
    a1i
    suppss2
    @19
    @3
    cvv
    cvv
    c.0
    suppssfifsupp
    syl12anc
    @5
    cP
    cR
    @4
    cB
    cI
    @3
    c.0
    mplmon.s
    @13
    @14
    mplmon.z
    mplmon.b
    mplelbas
    sylanbrc
end
