include "c0g.mm"
include "cmgp.mm"
include "ccom.mm"
include "cfv.mm"
include "cur.mm"
include "cprds.mm"
include "co.mm"
include "eqid.mm"
include "crg.mm"
include "cmnd.mm"
include "cres.mm"
include "wf.mm"
include "mgpf.mm"
include "fco2.mm"
include "sylancr.mm"
include "prds0g.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "cplusg.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "prdsmgp.mm"
include "simpld.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "simprd.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "eqtr4d.mm"
include "df-ur.mm"
include "coeq1i.mm"
include "coass.mm"
include "eqtri.mm"
include "ringidval.mm"
include "3eqtr4g.mm"

theorem prds1
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume prds1.y: |- Y = ( S Xs_ R )
  assume prds1.i: |- ( ph -> I e. W )
  assume prds1.s: |- ( ph -> S e. V )
  assume prds1.r: |- ( ph -> R : I --> Ring )


  assert |- ( ph -> ( 1r o. R ) = ( 1r ` Y ) )

  proof
    wph
    c0g
    cmgp
    cR
    ccom
    #
    ccom
    #
    cY
    cmgp
    cfv
    #
    c0g
    cfv
    #
    cur
    cR
    ccom
    #
    cY
    cur
    cfv
    #
    wph
    @1
    cS
    @0
    cprds
    co
    #
    c0g
    cfv
    @3
    wph
    @0
    cS
    cI
    cV
    cW
    @6
    @6
    eqid
    #
    prds1.i
    prds1.s
    wph
    crg
    cmnd
    cmgp
    crg
    cres
    wf
    cI
    crg
    cR
    wf
    #
    cI
    cmnd
    @0
    wf
    mgpf
    prds1.r
    cI
    crg
    cmnd
    cmgp
    cR
    fco2
    sylancr
    prds0g
    wph
    vx
    vy
    @2
    cbs
    cfv
    #
    @2
    @6
    wph
    @9
    eqidd
    wph
    @9
    @6
    cbs
    cfv
    wceq
    #
    @2
    cplusg
    cfv
    #
    @6
    cplusg
    cfv
    #
    wceq
    #
    wph
    cR
    cS
    cI
    @2
    cW
    cV
    cY
    @6
    prds1.y
    @2
    eqid
    #
    @7
    prds1.i
    prds1.s
    wph
    @8
    cR
    cI
    wfn
    prds1.r
    cI
    crg
    cR
    ffn
    syl
    prdsmgp
    #
    simpld
    wph
    vx
    cv
    @9
    wcel
    vy
    cv
    @9
    wcel
    wa
    vx
    vy
    @11
    @12
    wph
    @10
    @13
    @15
    simprd
    oveqdr
    grpidpropd
    eqtr4d
    @4
    c0g
    cmgp
    ccom
    #
    cR
    ccom
    @1
    cur
    @16
    cR
    df-ur
    coeq1i
    c0g
    cmgp
    cR
    coass
    eqtri
    cY
    @5
    @2
    @14
    @5
    eqid
    ringidval
    3eqtr4g
end
