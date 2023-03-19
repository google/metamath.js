include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "eqid.mm"
include "dprdfid.mm"
include "simprd.mm"
include "eqcomd.mm"
include "cdprd.mm"
include "dprdub.mm"
include "sseldd.mm"
include "simpld.mm"
include "dpjeq.mm"
include "mpbid.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wne.mm"
include "ifnefalse.mm"
include "syl.mm"
include "eqtrd.mm"

theorem dpjrid
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cC: class C
  let cQ: class Q
  let cW: class W
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjlid.3: |- ( ph -> X e. I )
  assume dpjlid.4: |- ( ph -> A e. ( S ` X ) )
  assume dpjrid.0: |- .0. = ( 0g ` G )
  assume dpjrid.5: |- ( ph -> Y e. I )
  assume dpjrid.6: |- ( ph -> Y =/= X )


  assert |- ( ph -> ( ( P ` Y ) ` A ) = .0. )

  proof
    wph
    cA
    cY
    cP
    cfv
    #
    cfv
    #
    cY
    cX
    wceq
    #
    cA
    c.0
    cif
    #
    c.0
    wph
    cY
    cI
    wcel
    cA
    vx
    cv
    #
    cP
    cfv
    #
    cfv
    #
    @4
    cX
    wceq
    #
    cA
    c.0
    cif
    #
    wceq
    #
    vx
    cI
    wral
    #
    @1
    @3
    wceq
    #
    dpjrid.5
    wph
    cA
    cG
    vx
    cI
    @8
    cmpt
    #
    cgsu
    co
    #
    wceq
    @10
    wph
    @13
    cA
    wph
    @12
    vh
    cv
    c.0
    cfsupp
    wbr
    vh
    vi
    cI
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    wcel
    #
    @13
    cA
    wceq
    #
    wph
    cA
    cS
    vh
    vi
    vx
    @12
    cG
    cI
    @14
    cX
    c.0
    dpjrid.0
    @14
    eqid
    #
    dpjfval.1
    dpjfval.2
    dpjlid.3
    dpjlid.4
    @12
    eqid
    dprdfid
    #
    simprd
    eqcomd
    wph
    vx
    cA
    @8
    cP
    cS
    vh
    vi
    cG
    cI
    @14
    c.0
    dpjfval.1
    dpjfval.2
    dpjfval.p
    wph
    cX
    cS
    cfv
    cG
    cS
    cdprd
    co
    cA
    wph
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjlid.3
    dprdub
    dpjlid.4
    sseldd
    dpjrid.0
    @17
    wph
    @15
    @16
    @18
    simpld
    dpjeq
    mpbid
    @9
    @11
    vx
    cY
    cI
    @4
    cY
    wceq
    #
    @6
    @1
    @8
    @3
    @19
    cA
    @5
    @0
    @4
    cY
    cP
    fveq2
    fveq1d
    @19
    @7
    @2
    cA
    c.0
    @4
    cY
    cX
    eqeq1
    ifbid
    eqeq12d
    rspcv
    sylc
    wph
    cY
    cX
    wne
    @3
    c.0
    wceq
    dpjrid.6
    cY
    cX
    cA
    c.0
    ifnefalse
    syl
    eqtrd
end
