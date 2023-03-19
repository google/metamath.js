include "cq.mm"
include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "qsscn.mm"
include "ccnfld.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"

theorem qrngbas
  let cQ: class Q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K
  let vj: setvar j
  let vx: setvar x
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let wph: wff ph
  let vg: setvar g
  let cJ: class J
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cA: class A
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )


  assert |- QQ = ( Base ` Q )

  proof
    cq
    cc
    wss
    cq
    cQ
    cbs
    cfv
    wceq
    qsscn
    cq
    cc
    cQ
    ccnfld
    qrng.q
    cnfldbas
    ressbas2
    ax-mp
end
