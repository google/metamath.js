include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cvv.mm"
include "dpjfval.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "reseq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem dpjval
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cC: class C
  let cW: class W
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjfval.q: |- Q = ( proj1 ` G )
  assume dpjval.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( P ` X ) = ( ( S ` X ) Q ( G DProd ( S |` ( I \ { X } ) ) ) ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cS
    cfv
    #
    cG
    cS
    cI
    @0
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cQ
    co
    cX
    cS
    cfv
    #
    cG
    cS
    cI
    cX
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cQ
    co
    cI
    cP
    cvv
    wph
    cP
    cQ
    cS
    vx
    cG
    cI
    dpjfval.1
    dpjfval.2
    dpjfval.p
    dpjfval.q
    dpjfval
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @1
    @6
    @5
    @10
    cQ
    @12
    @0
    cX
    cS
    wph
    @11
    simpr
    #
    fveq2d
    @12
    @4
    @9
    cG
    cdprd
    @12
    @3
    @8
    cS
    @12
    @2
    @7
    cI
    @12
    @0
    cX
    @13
    sneqd
    difeq2d
    reseq2d
    oveq2d
    oveq12d
    dpjval.3
    wph
    @6
    @10
    cQ
    ovexd
    fvmptd
end
