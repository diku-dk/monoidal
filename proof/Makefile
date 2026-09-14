.PHONY: all clean

all: ParensTupleDirect.vo

all: decimal.vo

decimal.vo: decimal.v Monoid.vo
	rocq compile decimal.v

Delimiter.vo: Delimiter.v
	rocq compile Delimiter.v

ParensTupleDirect.vo: ParensTupleDirect.v ParensTuple.vo
	rocq compile ParensTupleDirect.v

all: Monoid.vo arith.vo with_gen.vo with_obs.vo filter.vo opt.vo optone.vo nestable.vo count.vo all.vo Exists.vo nat.vo prod.vo dup.vo chunk.vo chunk2.vo float.vo Parens.vo parens_hom.vo PullArray.vo IndexedReplay.vo Parens_n.vo ParensRegions.vo ParensTuple.vo ParensTupleProof.vo

ParensTupleProof.vo: ParensTupleProof.v ParensTuple.vo Parens_n.vo ParensRegions.vo ParensTupleDirect.vo
	rocq compile ParensTupleProof.v

ParensRegions.vo: ParensRegions.v
	rocq compile ParensRegions.v

ParensTuple.vo: ParensTuple.v Monoid.vo Parens.vo Delimiter.vo ParensRegions.vo
	rocq compile ParensTuple.v

parens_hom.vo: parens_hom.v Monoid.vo Parens.vo
	rocq compile parens_hom.v

chunk2.vo: chunk2.v Monoid.vo chunk.vo
	rocq compile chunk2.v

optone.vo: optone.v Monoid.vo
	rocq compile optone.v

nestable.vo: nestable.v Monoid.vo Parens.vo
	rocq compile nestable.v

arith.vo: arith.v Monoid.vo
	rocq compile arith.v

with_gen.vo: with_gen.v Monoid.vo
	rocq compile with_gen.v

with_obs.vo: with_obs.v Monoid.vo
	rocq compile with_obs.v

filter.vo: filter.v Monoid.vo with_obs.vo
	rocq compile filter.v

opt.vo: opt.v Monoid.vo
	rocq compile opt.v

count.vo: count.v Monoid.vo arith.vo
	rocq compile count.v

all.vo: all.v Monoid.vo
	rocq compile all.v

Exists.vo: Exists.v Monoid.vo
	rocq compile Exists.v

Monoid.vo: Monoid.v
	rocq compile Monoid.v

nat.vo: nat.v Monoid.vo
	rocq compile nat.v

prod.vo: prod.v Monoid.vo
	rocq compile prod.v

dup.vo: dup.v Monoid.vo prod.vo
	rocq compile dup.v

chunk.vo: chunk.v Monoid.vo
	rocq compile chunk.v

float.vo: float.v Monoid.vo
	rocq compile float.v

Parens.vo: Parens.v Monoid.vo
	rocq compile Parens.v

PullArray.vo: PullArray.v
	rocq compile PullArray.v

IndexedReplay.vo: IndexedReplay.v
	rocq compile IndexedReplay.v

Parens_n.vo: Parens_n.v Monoid.vo Parens.vo PullArray.vo IndexedReplay.vo Delimiter.vo
	rocq compile Parens_n.v

clean:
	rm -f decimal.glob decimal.vo decimal.vok decimal.vos .decimal.aux
	rm -f Delimiter.glob Delimiter.vo Delimiter.vok Delimiter.vos .Delimiter.aux ParensTupleDirect.glob ParensTupleDirect.vo ParensTupleDirect.vok ParensTupleDirect.vos .ParensTupleDirect.aux
	rm -f ParensTupleProof.glob ParensTupleProof.vo ParensTupleProof.vok ParensTupleProof.vos .ParensTupleProof.aux
	rm -f ParensRegions.glob ParensRegions.vo ParensRegions.vok ParensRegions.vos .ParensRegions.aux
	rm -f ParensTuple.glob ParensTuple.vo ParensTuple.vok ParensTuple.vos .ParensTuple.aux
	rm -f optone.glob optone.vo optone.vok optone.vos .optone.aux
	rm -f nestable.glob nestable.vo nestable.vok nestable.vos .nestable.aux
	rm -f IndexedReplay.glob IndexedReplay.vo IndexedReplay.vok IndexedReplay.vos .IndexedReplay.aux
	rm -f *~
	rm -f arith.glob arith.vo arith.vok arith.vos .arith.aux
	rm -f with_gen.glob with_gen.vo with_gen.vok with_gen.vos .with_gen.aux
	rm -f with_obs.glob with_obs.vo with_obs.vok with_obs.vos .with_obs.aux
	rm -f filter.glob filter.vo filter.vok filter.vos .filter.aux
	rm -f opt.glob opt.vo opt.vok opt.vos .opt.aux
	rm -f count.glob count.vo count.vok count.vos .count.aux
	rm -f all.glob all.vo all.vok all.vos .all.aux
	rm -f Exists.glob Exists.vo Exists.vok Exists.vos .Exists.aux
	rm -f float.glob float.vo float.vok float.vos .float.aux
	rm -f chunk.glob chunk.vo chunk.vok chunk.vos .chunk.aux
	rm -f prod.glob prod.vo prod.vok prod.vos .prod.aux
	rm -f dup.glob dup.vo dup.vok dup.vos .dup.aux
	rm -f nat.glob nat.vo nat.vok nat.vos .nat.aux
	rm -f Monoid.glob Monoid.vo Monoid.vok Monoid.vos .Monoid.aux
	rm -f Parens.glob Parens.vo Parens.vok Parens.vos .Parens.aux \
	      Parens_n.glob Parens_n.vo Parens_n.vok Parens_n.vos .Parens_n.aux
	rm -f PullArray.glob PullArray.vo PullArray.vok PullArray.vos .PullArray.aux
	rm -f parens_hom.glob parens_hom.vo chunk2.glob chunk2.vo
