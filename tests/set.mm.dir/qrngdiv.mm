include "cq.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cdvr.mm"
include "cfv.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "cress.mm"
include "cdr.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "a1i.mm"
include "simp1.mm"
include "wa.mm"
include "3simpc.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "cnflddiv.mm"
include "qrngbas.mm"
include "qrng0.mm"
include "qdrng.mm"
include "drngui.mm"
include "eqid.mm"
include "subrgdv.mm"
include "syl3anc.mm"
include "eqcomd.mm"

theorem qrngdiv
  let cQ: class Q
  let cX: class X
  let cY: class Y
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
  let cF: class F
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )


  assert |- ( ( X e. QQ /\ Y e. QQ /\ Y =/= 0 ) -> ( X ( /r ` Q ) Y ) = ( X / Y ) )

  proof
    cX
    cq
    wcel
    #
    cY
    cq
    wcel
    #
    cY
    cc0
    wne
    #
    w3a
    #
    cX
    cY
    cdiv
    co
    #
    cX
    cY
    cQ
    cdvr
    cfv
    #
    co
    #
    @3
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    cY
    cq
    cc0
    csn
    cdif
    #
    wcel
    #
    @4
    @6
    wceq
    @7
    @3
    @7
    ccnfld
    cq
    cress
    co
    cdr
    wcel
    qsubdrg
    simpli
    a1i
    @0
    @1
    @2
    simp1
    @3
    @1
    @2
    wa
    @9
    @0
    @1
    @2
    3simpc
    cY
    cq
    cc0
    eldifsn
    sylibr
    cq
    cdiv
    ccnfld
    cQ
    @8
    @5
    cX
    cY
    qrng.q
    cnflddiv
    cq
    cQ
    cc0
    cQ
    qrng.q
    qrngbas
    cQ
    qrng.q
    qrng0
    cQ
    qrng.q
    qdrng
    drngui
    @5
    eqid
    subrgdv
    syl3anc
    eqcomd
end
