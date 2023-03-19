include "cr.mm"
include "wss.mm"
include "cc0.mm"
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
include "covol.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "ssrab2.mm"
include "0xr.mm"
include "infxrgelb.mm"
include "mp2an.mm"
include "eqid.mm"
include "ovolmge0.mm"
include "mprgbir.mm"
include "ovolval.mm"
include "syl5breqr.mm"

theorem ovolge0
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


  assert |- ( A C_ RR -> 0 <_ ( vol* ` A ) )

  proof
    cA
    cr
    wss
    cc0
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
    cA
    covol
    cfv
    cle
    cc0
    @3
    cle
    wbr
    #
    cc0
    vx
    cv
    #
    cle
    wbr
    #
    vx
    @2
    @2
    cxr
    wss
    cc0
    cxr
    wcel
    @4
    @6
    vx
    @2
    wral
    wb
    @1
    vy
    cxr
    ssrab2
    0xr
    vx
    @2
    cc0
    infxrgelb
    mp2an
    vy
    cA
    @5
    vf
    @2
    @2
    eqid
    #
    ovolmge0
    mprgbir
    vy
    cA
    vf
    @2
    @7
    ovolval
    syl5breqr
end
