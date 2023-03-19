include "cq.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cminusg.mm"
include "cfv.mm"
include "cneg.mm"
include "csubg.mm"
include "wceq.mm"
include "csubrg.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "subginv.mm"
include "mpan.mm"
include "cc.mm"
include "qcn.mm"
include "cnfldneg.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem qrngneg
  let cQ: class Q
  let cX: class X
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
  let cA: class A
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )


  assert |- ( X e. QQ -> ( ( invg ` Q ) ` X ) = -u X )

  proof
    cX
    cq
    wcel
    #
    cX
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    cX
    cQ
    cminusg
    cfv
    #
    cfv
    #
    cX
    cneg
    #
    cq
    ccnfld
    csubg
    cfv
    wcel
    #
    @0
    @2
    @4
    wceq
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    @6
    @7
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
    ax-mp
    cq
    ccnfld
    cQ
    @1
    @3
    cX
    qrng.q
    @1
    eqid
    @3
    eqid
    subginv
    mpan
    @0
    cX
    cc
    wcel
    @2
    @5
    wceq
    cX
    qcn
    cX
    cnfldneg
    syl
    eqtr3d
end
