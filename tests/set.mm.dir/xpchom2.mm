include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cxp.mm"
include "xpcbas.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "xpchom.mm"
include "wceq.mm"
include "op1stg.mm"
include "oveq12d.mm"
include "op2ndg.mm"
include "xpeq12d.mm"
include "eqtrd.mm"

theorem xpchom2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume xpcco2.t: |- T = ( C Xc. D )
  assume xpcco2.x: |- X = ( Base ` C )
  assume xpcco2.y: |- Y = ( Base ` D )
  assume xpcco2.h: |- H = ( Hom ` C )
  assume xpcco2.j: |- J = ( Hom ` D )
  assume xpcco2.m: |- ( ph -> M e. X )
  assume xpcco2.n: |- ( ph -> N e. Y )
  assume xpcco2.p: |- ( ph -> P e. X )
  assume xpcco2.q: |- ( ph -> Q e. Y )
  assume xpchom2.k: |- K = ( Hom ` T )


  assert |- ( ph -> ( <. M , N >. K <. P , Q >. ) = ( ( M H P ) X. ( N J Q ) ) )

  proof
    wph
    cM
    cN
    cop
    #
    cP
    cQ
    cop
    #
    cK
    co
    @0
    c1st
    cfv
    #
    @1
    c1st
    cfv
    #
    cH
    co
    #
    @0
    c2nd
    cfv
    #
    @1
    c2nd
    cfv
    #
    cJ
    co
    #
    cxp
    cM
    cP
    cH
    co
    #
    cN
    cQ
    cJ
    co
    #
    cxp
    wph
    cX
    cY
    cxp
    #
    cC
    cD
    cT
    cH
    cJ
    cK
    @0
    @1
    xpcco2.t
    cC
    cD
    cT
    cX
    cY
    xpcco2.t
    xpcco2.x
    xpcco2.y
    xpcbas
    xpcco2.h
    xpcco2.j
    xpchom2.k
    wph
    cM
    cX
    wcel
    #
    cN
    cY
    wcel
    #
    @0
    @10
    wcel
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    opelxpi
    syl2anc
    wph
    cP
    cX
    wcel
    #
    cQ
    cY
    wcel
    #
    @1
    @10
    wcel
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    opelxpi
    syl2anc
    xpchom
    wph
    @4
    @8
    @7
    @9
    wph
    @2
    cM
    @3
    cP
    cH
    wph
    @11
    @12
    @2
    cM
    wceq
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    op1stg
    syl2anc
    wph
    @13
    @14
    @3
    cP
    wceq
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    op1stg
    syl2anc
    oveq12d
    wph
    @5
    cN
    @6
    cQ
    cJ
    wph
    @11
    @12
    @5
    cN
    wceq
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    op2ndg
    syl2anc
    wph
    @13
    @14
    @6
    cQ
    wceq
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    op2ndg
    syl2anc
    oveq12d
    xpeq12d
    eqtrd
end
