include "cq.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cc0.mm"
include "c0g.mm"
include "wceq.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "cnfld0.mm"
include "subg0.mm"
include "mp2b.mm"

theorem qrng0
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


  assert |- 0 = ( 0g ` Q )

  proof
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    cq
    ccnfld
    csubg
    cfv
    wcel
    cc0
    cQ
    c0g
    cfv
    wceq
    @0
    ccnfld
    cq
    cress
    co
    cdr
    wcel
    qsubdrg
    simpli
    cq
    ccnfld
    subrgsubg
    cq
    ccnfld
    cQ
    cc0
    qrng.q
    cnfld0
    subg0
    mp2b
end
