include "wcel.mm"
include "wa.mm"
include "ccrg.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "a1i.mm"
include "wss.mm"
include "difssd.mm"
include "anim2i.mm"
include "adantr.mm"
include "submabas.mm"
include "syl.mm"
include "simpr.mm"
include "eqid.mm"
include "madetsmelbas2.mm"
include "syl3anc.mm"

theorem smadiadetlem3lem0
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vq: setvar q
  let cL: class L
  let vp: setvar p
  assume marep01ma.a: |- A = ( N Mat R )
  assume marep01ma.b: |- B = ( Base ` A )
  assume marep01ma.r: |- R e. CRing
  assume marep01ma.0: |- .0. = ( 0g ` R )
  assume marep01ma.1: |- .1. = ( 1r ` R )
  assume smadiadetlem.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume smadiadetlem.g: |- G = ( mulGrp ` R )
  assume madetminlem.y: |- Y = ( ZRHom ` R )
  assume madetminlem.s: |- S = ( pmSgn ` N )
  assume madetminlem.t: |- .x. = ( .r ` R )
  assume smadiadetlem.w: |- W = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume smadiadetlem.z: |- Z = ( pmSgn ` ( N \ { K } ) )

  disjoint i j
  disjoint i n
  disjoint B i
  disjoint j n
  disjoint B j
  disjoint B n
  disjoint K i
  disjoint K j
  disjoint K n
  disjoint M i
  disjoint M j
  disjoint M n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint P i
  disjoint P j
  disjoint P n
  disjoint Q i
  disjoint Q j
  disjoint Q n
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint .1. i
  disjoint .1. j
  disjoint .1. n
  disjoint .0. i
  disjoint .0. j
  disjoint .0. n
  disjoint G n
  disjoint W n
  disjoint k l
  disjoint B k
  disjoint B l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint i m
  disjoint j m
  disjoint m n
  disjoint B m
  disjoint i q
  disjoint j q
  disjoint m q
  disjoint K m
  disjoint n q
  disjoint K q
  disjoint L i
  disjoint L j
  disjoint L m
  disjoint L n
  disjoint L q
  disjoint M m
  disjoint N m
  disjoint P m
  disjoint P q
  disjoint Q m
  disjoint Q q
  disjoint R m
  disjoint .1. m
  disjoint .0. m
  disjoint G m
  disjoint n p
  disjoint B p
  disjoint K p
  disjoint L p
  disjoint M p
  disjoint N p
  disjoint P p
  disjoint R p
  disjoint i p
  disjoint j p
  disjoint p q
  assert |- ( ( ( M e. B /\ K e. N ) /\ Q e. W ) -> ( ( ( Y o. Z ) ` Q ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( Q ` n ) ) ) ) ) e. ( Base ` R ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cQ
    cW
    wcel
    #
    wa
    #
    cR
    ccrg
    wcel
    #
    vi
    vj
    cN
    cK
    csn
    #
    cdif
    #
    @7
    vi
    cv
    vj
    cv
    cM
    co
    cmpt2
    #
    @7
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    cQ
    cY
    cZ
    ccom
    cfv
    cG
    vn
    @7
    vn
    cv
    #
    @12
    cQ
    cfv
    @8
    co
    cmpt
    cgsu
    co
    cR
    cmulr
    cfv
    co
    cR
    cbs
    cfv
    wcel
    @5
    @4
    marep01ma.r
    a1i
    @4
    @0
    @7
    cN
    wss
    #
    wa
    #
    @11
    @2
    @14
    @3
    @1
    @13
    @0
    @1
    cN
    @6
    difssd
    anim2i
    adantr
    cA
    cB
    @7
    cR
    vi
    vj
    cM
    cN
    marep01ma.a
    marep01ma.b
    submabas
    syl
    @2
    @3
    simpr
    @9
    @10
    cW
    cQ
    cR
    cZ
    vn
    cG
    @8
    @7
    cY
    smadiadetlem.w
    smadiadetlem.z
    madetminlem.y
    @9
    eqid
    @10
    eqid
    smadiadetlem.g
    madetsmelbas2
    syl3anc
end
