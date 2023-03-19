include "cq.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cur.mm"
include "wceq.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "cnfld1.mm"
include "subrg1.mm"
include "ax-mp.mm"

theorem qrng1
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


  assert |- 1 = ( 1r ` Q )

  proof
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    c1
    cQ
    cur
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
    cQ
    c1
    qrng.q
    cnfld1
    subrg1
    ax-mp
end
