include "ccnfld.mm"
include "cq.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "qsubdrg.mm"
include "simpri.mm"
include "eqeltri.mm"

theorem qdrng
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


  assert |- Q e. DivRing

  proof
    cQ
    ccnfld
    cq
    cress
    co
    #
    cdr
    qrng.q
    cq
    ccnfld
    csubrg
    cfv
    wcel
    @0
    cdr
    wcel
    qsubdrg
    simpri
    eqeltri
end
