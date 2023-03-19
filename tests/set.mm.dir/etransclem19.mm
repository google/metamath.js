include "cfv.mm"
include "cdvn.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "cn0.mm"
include "0red.mm"
include "zred.mm"
include "cr.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0red.mm"
include "nnred.mm"
include "ifcld.mm"
include "wa.mm"
include "nn0ge0d.mm"
include "adantr.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "nnnn0d.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "lelttrd.mm"
include "ltled.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "etransclem17.mm"
include "iftrued.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"

theorem etransclem19
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  assume etransclem19.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem19.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem19.p: |- ( ph -> P e. NN )
  assume etransclem19.1: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem19.J: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem19.n: |- ( ph -> N e. ZZ )
  assume etransclem19.7: |- ( ph -> if ( J = 0 , ( P - 1 ) , P ) < N )

  disjoint J j
  disjoint J x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( S Dn ( H ` J ) ) ` N ) = ( x e. X |-> 0 ) )

  proof
    wph
    cN
    cS
    cJ
    cH
    cfv
    cdvn
    co
    cfv
    vx
    cX
    cJ
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cN
    clt
    wbr
    #
    cc0
    @2
    cfa
    cfv
    @2
    cN
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    vx
    cv
    cJ
    cmin
    co
    @4
    cexp
    co
    cmul
    co
    #
    cif
    #
    cmpt
    vx
    cX
    cc0
    cmpt
    wph
    vx
    cP
    cS
    vj
    cH
    cJ
    cM
    cN
    cX
    etransclem19.s
    etransclem19.x
    etransclem19.p
    etransclem19.1
    etransclem19.J
    wph
    cN
    cz
    wcel
    cc0
    cN
    cle
    wbr
    cN
    cn0
    wcel
    etransclem19.n
    wph
    cc0
    cN
    wph
    0red
    #
    wph
    cN
    etransclem19.n
    zred
    #
    wph
    cc0
    @2
    cN
    @7
    wph
    @0
    @1
    cP
    cr
    wph
    @1
    wph
    cP
    cn
    wcel
    @1
    cn0
    wcel
    etransclem19.p
    cP
    nnm1nn0
    syl
    #
    nn0red
    wph
    cP
    etransclem19.p
    nnred
    ifcld
    @8
    wph
    @0
    cc0
    @2
    cle
    wbr
    wph
    @0
    wa
    cc0
    @1
    @2
    cle
    wph
    cc0
    @1
    cle
    wbr
    @0
    wph
    @1
    @9
    nn0ge0d
    adantr
    @0
    @1
    @2
    wceq
    wph
    @0
    @2
    @1
    @0
    @1
    cP
    iftrue
    eqcomd
    adantl
    breqtrd
    wph
    @0
    wn
    #
    wa
    cc0
    cP
    @2
    cle
    wph
    cc0
    cP
    cle
    wbr
    @10
    wph
    cP
    wph
    cP
    etransclem19.p
    nnnn0d
    nn0ge0d
    adantr
    @10
    cP
    @2
    wceq
    wph
    @10
    @2
    cP
    @0
    @1
    cP
    iffalse
    eqcomd
    adantl
    breqtrd
    pm2.61dan
    etransclem19.7
    lelttrd
    ltled
    cN
    elnn0z
    sylanbrc
    etransclem17
    wph
    vx
    cX
    @6
    cc0
    wph
    @3
    cc0
    @5
    etransclem19.7
    iftrued
    mpteq2dv
    eqtrd
end
