include "cn.mm"
include "cr.mm"
include "cvma.mm"
include "wf.mm"
include "wtru.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cuni.mm"
include "clog.mm"
include "cc0.mm"
include "cif.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "csbex.mm"
include "a1i.mm"
include "cmpt.mm"
include "df-vma.mm"
include "vmacl.mm"
include "adantl.mm"
include "fmpt2d.mm"
include "trud.mm"

theorem vmaf
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- Lam : NN --> RR

  proof
    cn
    cr
    cvma
    wf
    wtru
    vx
    vn
    cn
    vs
    vp
    cv
    vx
    cv
    #
    cdvds
    wbr
    vp
    cprime
    crab
    #
    vs
    cv
    #
    chash
    cfv
    c1
    wceq
    #
    @2
    cuni
    #
    clog
    cfv
    #
    cc0
    cif
    #
    csb
    #
    cr
    cvma
    cvv
    @7
    cvv
    wcel
    wtru
    @0
    cn
    wcel
    wa
    vs
    @1
    @6
    @3
    @5
    cc0
    @4
    clog
    fvex
    c0ex
    ifex
    csbex
    a1i
    cvma
    vx
    cn
    @7
    cmpt
    wceq
    wtru
    vx
    vs
    vp
    df-vma
    a1i
    vn
    cv
    #
    cn
    wcel
    @8
    cvma
    cfv
    cr
    wcel
    wtru
    @8
    vmacl
    adantl
    fmpt2d
    trud
end
