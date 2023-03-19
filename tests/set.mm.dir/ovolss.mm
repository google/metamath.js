include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
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
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "ovolsslem.mm"

theorem ovolss
  let cA: class A
  let cB: class B
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
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- ( ( A C_ B /\ B C_ RR ) -> ( vol* ` A ) <_ ( vol* ` B ) )

  proof
    vy
    cA
    cB
    vf
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    #
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
    #
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
    #
    wrex
    vy
    cxr
    crab
    #
    cB
    @1
    wss
    @2
    wa
    vf
    @3
    wrex
    vy
    cxr
    crab
    #
    @4
    eqid
    @5
    eqid
    ovolsslem
end
