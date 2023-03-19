include "csn.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cdif.mm"
include "cin.mm"
include "cfv.mm"
include "dpjlem.mm"
include "ineq1d.mm"
include "cdm.mm"
include "wbr.mm"
include "wa.mm"
include "ccntz.mm"
include "wss.mm"
include "wceq.mm"
include "w3a.mm"
include "dprdf2.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "undif2.mm"
include "snssd.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "eqid.mm"
include "dmdprdsplit.mm"
include "mpbid.mm"
include "simp3d.mm"
include "eqtr3d.mm"

theorem dpjdisj
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let c.0: class .0.
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cP: class P
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjlem.3: |- ( ph -> X e. I )
  assume dpjdisj.0: |- .0. = ( 0g ` G )


  assert |- ( ph -> ( ( S ` X ) i^i ( G DProd ( S |` ( I \ { X } ) ) ) ) = { .0. } )

  proof
    wph
    cG
    cS
    cX
    csn
    #
    cres
    #
    cdprd
    co
    #
    cG
    cS
    cI
    @0
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cin
    #
    cX
    cS
    cfv
    #
    @5
    cin
    c.0
    csn
    #
    wph
    @2
    @7
    @5
    wph
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjlem.3
    dpjlem
    ineq1d
    wph
    cG
    @1
    cdprd
    cdm
    #
    wbr
    cG
    @4
    @9
    wbr
    wa
    #
    @2
    @5
    cG
    ccntz
    cfv
    #
    cfv
    wss
    #
    @6
    @8
    wceq
    #
    wph
    cG
    cS
    @9
    wbr
    @10
    @12
    @13
    w3a
    dpjfval.1
    wph
    @0
    @3
    cS
    cG
    cI
    c.0
    @11
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprdf2
    @0
    @3
    cin
    c0
    wceq
    wph
    @0
    cI
    disjdif
    a1i
    wph
    @0
    @3
    cun
    @0
    cI
    cun
    #
    cI
    @0
    cI
    undif2
    wph
    @0
    cI
    wss
    @14
    cI
    wceq
    wph
    cX
    cI
    dpjlem.3
    snssd
    @0
    cI
    ssequn1
    sylib
    syl5req
    @11
    eqid
    dpjdisj.0
    dmdprdsplit
    mpbid
    simp3d
    eqtr3d
end
