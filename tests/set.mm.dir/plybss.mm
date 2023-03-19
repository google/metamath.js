include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cdm.mm"
include "cpw.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "df-ply.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "elpwid.mm"

theorem plybss
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T


  assert |- ( F e. ( Poly ` S ) -> S C_ CC )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cS
    cc
    @0
    cply
    cdm
    cc
    cpw
    #
    cS
    vx
    @1
    vf
    cv
    vz
    cc
    cc0
    vn
    cv
    cfz
    co
    vk
    cv
    #
    va
    cv
    cfv
    vz
    cv
    @2
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    wceq
    va
    vx
    cv
    cc0
    csn
    cun
    cn0
    cmap
    co
    wrex
    vn
    cn0
    wrex
    vf
    cab
    cply
    vx
    vz
    vf
    vk
    vn
    va
    df-ply
    dmmptss
    cF
    cS
    cply
    elfvdm
    sseldi
    elpwid
end
