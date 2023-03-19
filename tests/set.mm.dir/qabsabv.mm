include "cabs.mm"
include "ccnfld.mm"
include "cabv.mm"
include "cfv.mm"
include "wcel.mm"
include "cq.mm"
include "csubrg.mm"
include "cres.mm"
include "absabv.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "eqid.mm"
include "abvres.mm"
include "mp2an.mm"

theorem qabsabv
  let cA: class A
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
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )


  assert |- ( abs |` QQ ) e. A

  proof
    cabs
    ccnfld
    cabv
    cfv
    #
    wcel
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    cabs
    cq
    cres
    cA
    wcel
    absabv
    @1
    ccnfld
    cq
    cress
    co
    cdr
    wcel
    qsubdrg
    simpli
    @0
    cA
    cq
    ccnfld
    cQ
    cabs
    @0
    eqid
    qrng.q
    qabsabv.a
    abvres
    mp2an
end
