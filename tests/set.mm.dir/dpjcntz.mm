include "cfv.mm"
include "csn.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cdif.mm"
include "dpjlem.mm"
include "cdm.mm"
include "wbr.mm"
include "wa.mm"
include "wss.mm"
include "cin.mm"
include "c0g.mm"
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
include "simp2d.mm"
include "eqsstr3d.mm"

theorem dpjcntz
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let cZ: class Z
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let c.0: class .0.
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
  assume dpjcntz.z: |- Z = ( Cntz ` G )


  assert |- ( ph -> ( S ` X ) C_ ( Z ` ( G DProd ( S |` ( I \ { X } ) ) ) ) )

  proof
    wph
    cX
    cS
    cfv
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
    cZ
    cfv
    #
    wph
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjlem.3
    dpjlem
    wph
    cG
    @1
    cdprd
    cdm
    #
    wbr
    cG
    @4
    @7
    wbr
    wa
    #
    @2
    @6
    wss
    #
    @2
    @5
    cin
    cG
    c0g
    cfv
    #
    csn
    wceq
    #
    wph
    cG
    cS
    @7
    wbr
    @8
    @9
    @11
    w3a
    dpjfval.1
    wph
    @0
    @3
    cS
    cG
    cI
    @10
    cZ
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
    @12
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
    dpjcntz.z
    @10
    eqid
    dmdprdsplit
    mpbid
    simp2d
    eqsstr3d
end
