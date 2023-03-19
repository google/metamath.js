include "crn.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "cmrex.mm"
include "cfv.mm"
include "cmvar.mm"
include "cpm.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "cmsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "eqid.mm"
include "msubff.mm"
include "frn.mm"
include "3syl.mm"
include "id.mm"
include "sseldd.mm"
include "elmapi.mm"
include "syl.mm"

theorem msubf
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume msubco.s: |- S = ( mSubst ` T )
  assume msubf.e: |- E = ( mEx ` T )


  assert |- ( F e. ran S -> F : E --> E )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cF
    cE
    cE
    cmap
    co
    #
    wcel
    cE
    cE
    cF
    wf
    @1
    @0
    @2
    cF
    @1
    cT
    cvv
    wcel
    #
    cT
    cmrex
    cfv
    #
    cT
    cmvar
    cfv
    #
    cpm
    co
    #
    @2
    cS
    wf
    @0
    @2
    wss
    @1
    @0
    c0
    wceq
    @3
    @0
    cF
    n0i
    @3
    wn
    #
    @0
    c0
    crn
    c0
    @7
    cS
    c0
    @7
    cS
    cT
    cmsub
    cfv
    c0
    msubco.s
    cT
    cmsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    @4
    cS
    cT
    cE
    @5
    cvv
    @5
    eqid
    @4
    eqid
    msubco.s
    msubf.e
    msubff
    @6
    @2
    cS
    frn
    3syl
    @1
    id
    sseldd
    cF
    cE
    cE
    elmapi
    syl
end
