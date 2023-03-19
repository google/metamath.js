include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "csb.mm"
include "cif.mm"
include "wceq.mm"
include "eqid.mm"
include "cdleme31sn.mm"
include "adantr.mm"
include "cv.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "iftrue.mm"
include "csbeq2i.mm"
include "syl6eq.mm"
include "wnfc.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfim.mm"
include "nfral.mm"
include "nfriota.mm"
include "a1i.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "csbiegf.mm"
include "sylan9eqr.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem cdleme31sn1
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cG: class G
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let vs: setvar s
  assume cdleme31sn1.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme31sn1.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme31sn1.c: |- C = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = [_ R / s ]_ G ) )

  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint .\/ s
  disjoint .<_ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint W s
  assert |- ( ( R e. A /\ R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N = C )

  proof
    cR
    cA
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vs
    cR
    cN
    csb
    #
    @2
    vs
    cR
    cI
    csb
    #
    vs
    cR
    cD
    csb
    #
    cif
    #
    cC
    @0
    @4
    @7
    wceq
    @2
    cA
    @7
    cD
    cP
    cQ
    cR
    cI
    c.or
    c.le
    cN
    vs
    cdleme31sn1.n
    @7
    eqid
    cdleme31sn
    adantr
    @3
    @7
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @8
    @1
    c.le
    wbr
    wn
    wa
    #
    vy
    cv
    #
    vs
    cR
    cG
    csb
    #
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    #
    cC
    @2
    @0
    @7
    vs
    cR
    @9
    @10
    cG
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    #
    csb
    #
    @15
    @2
    @7
    @5
    @20
    @2
    @5
    @6
    iftrue
    vs
    cR
    cI
    @19
    cdleme31sn1.i
    csbeq2i
    syl6eq
    vs
    cR
    @19
    @15
    cA
    vs
    @15
    wnfc
    @0
    @14
    vs
    vy
    cB
    @13
    vs
    vt
    cA
    vs
    cA
    nfcv
    @9
    @12
    vs
    @9
    vs
    nfv
    vs
    @10
    @11
    vs
    cR
    cG
    nfcsb1v
    nfeq2
    nfim
    nfral
    vs
    cB
    nfcv
    nfriota
    a1i
    vs
    cv
    cR
    wceq
    #
    @18
    @14
    vy
    cB
    @21
    @17
    @13
    vt
    cA
    @21
    @16
    @12
    @9
    @21
    cG
    @11
    @10
    vs
    cR
    cG
    csbeq1a
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    csbiegf
    sylan9eqr
    cdleme31sn1.c
    syl6eqr
    eqtrd
end
