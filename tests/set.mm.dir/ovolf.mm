include "cr.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "covol.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cioo.mm"
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
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "cinf.mm"
include "xrltso.mm"
include "infex.mm"
include "df-ovol.mm"
include "fnmpti.mm"
include "elpwi.mm"
include "wbr.mm"
include "ovolcl.mm"
include "ovolge0.mm"
include "pnfge.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem ovolf
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- vol* : ~P RR --> ( 0 [,] +oo )

  proof
    cr
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    covol
    wf
    covol
    @0
    wfn
    vx
    cv
    #
    covol
    cfv
    #
    @1
    wcel
    #
    vx
    @0
    wral
    vx
    @0
    @2
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
    @5
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
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    covol
    cxr
    @6
    clt
    xrltso
    infex
    vx
    vy
    vf
    df-ovol
    fnmpti
    @4
    vx
    @0
    @2
    @0
    wcel
    @2
    cr
    wss
    #
    @4
    @2
    cr
    elpwi
    @7
    @3
    cxr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cpnf
    cle
    wbr
    #
    @4
    @2
    ovolcl
    #
    @2
    ovolge0
    @7
    @8
    @10
    @11
    @3
    pnfge
    syl
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @4
    @8
    @9
    @10
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @3
    elicc1
    mp2an
    syl3anbrc
    syl
    rgen
    vx
    @0
    @1
    covol
    ffnfv
    mpbir2an
end
