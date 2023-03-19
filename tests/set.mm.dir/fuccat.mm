include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "cfunc.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqid.mm"
include "fuccatid.mm"
include "simpld.mm"

theorem fuccat
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let c.1: class .1.
  let vf: setvar f
  assume fuccat.q: |- Q = ( C FuncCat D )
  assume fuccat.r: |- ( ph -> C e. Cat )
  assume fuccat.s: |- ( ph -> D e. Cat )


  assert |- ( ph -> Q e. Cat )

  proof
    wph
    cQ
    ccat
    wcel
    cQ
    ccid
    cfv
    vf
    cC
    cD
    cfunc
    co
    cD
    ccid
    cfv
    #
    vf
    cv
    c1st
    cfv
    ccom
    cmpt
    wceq
    wph
    cC
    cD
    cQ
    @0
    vf
    fuccat.q
    fuccat.r
    fuccat.s
    @0
    eqid
    fuccatid
    simpld
end
