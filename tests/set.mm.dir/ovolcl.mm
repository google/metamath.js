include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "cinf.mm"
include "eqid.mm"
include "ovolval.mm"
include "wcel.mm"
include "ssrab2.mm"
include "infxrcl.mm"
include "ax-mp.mm"
include "syl6eqel.mm"

theorem ovolcl
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- ( A C_ RR -> ( vol* ` A ) e. RR* )

  proof
    cA
    cr
    wss
    cA
    covol
    cfv
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    vy
    cv
    caddc
    cabs
    cmin
    ccom
    @0
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    wa
    vf
    cle
    cr
    cr
    cxp
    cin
    cn
    cmap
    co
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cxr
    vy
    cA
    vf
    @2
    @2
    eqid
    ovolval
    @2
    cxr
    wss
    @3
    cxr
    wcel
    @1
    vy
    cxr
    ssrab2
    @2
    infxrcl
    ax-mp
    syl6eqel
end
